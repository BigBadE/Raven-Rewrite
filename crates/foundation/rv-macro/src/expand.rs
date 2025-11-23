//! Macro expansion engine

use crate::ast::{
    Delimiter, FragmentKind, MacroDef, MacroExpander, MacroId, MacroKind, MacroMatcher,
    MacroRule, SequenceKind, Token, TokenStream,
};
use crate::builtins;
use crate::error::MacroExpansionError;
use rv_intern::{Interner, Symbol};
use rv_span::FileSpan;
use rustc_hash::FxHashMap;

/// Bindings collected during pattern matching
type Bindings = FxHashMap<Symbol, Binding>;

/// A binding for a metavariable
#[derive(Debug, Clone)]
enum Binding {
    /// Single token sequence
    Single(TokenStream),
    /// Sequence of token sequences
    Multiple(Vec<TokenStream>),
}

/// Macro expansion context
pub struct MacroExpansionContext {
    /// Available macros
    macros: FxHashMap<Symbol, MacroDef>,
    /// Expansion stack (for recursion detection)
    expansion_stack: Vec<MacroId>,
    /// Maximum expansion depth
    max_depth: usize,
    /// String interner
    interner: Interner,
}

impl MacroExpansionContext {
    /// Create a new macro expansion context
    #[must_use]
    pub fn new(interner: Interner) -> Self {
        Self {
            macros: FxHashMap::default(),
            expansion_stack: Vec::new(),
            max_depth: 128,
            interner,
        }
    }

    /// Register a macro definition
    pub fn register_macro(&mut self, macro_def: MacroDef) {
        self.macros.insert(macro_def.name, macro_def);
    }

    /// Expand a macro invocation
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Macro is not found
    /// - Recursion limit is exceeded
    /// - No rule matches the arguments
    /// - Expansion fails
    pub fn expand_macro(
        &mut self,
        name: Symbol,
        arguments: TokenStream,
        span: FileSpan,
    ) -> Result<TokenStream, MacroExpansionError> {
        // Look up macro definition
        let macro_def = self
            .macros
            .get(&name)
            .ok_or(MacroExpansionError::UndefinedMacro { name, span })?
            .clone();

        // Check recursion depth
        if self.expansion_stack.len() >= self.max_depth {
            return Err(MacroExpansionError::RecursionLimit {
                macro_id: macro_def.id,
                span,
            });
        }

        // Push to expansion stack
        self.expansion_stack.push(macro_def.id);

        // Dispatch to expansion method
        let result = match &macro_def.kind {
            MacroKind::Declarative { rules } => {
                self.expand_declarative(rules, arguments, name, span)
            }
            MacroKind::Builtin { expander } => {
                builtins::expand_builtin(*expander, arguments, span, &self.interner)
            }
        };

        // Pop from expansion stack
        self.expansion_stack.pop();

        result
    }

    /// Expand a declarative macro (macro_rules!)
    fn expand_declarative(
        &mut self,
        rules: &[MacroRule],
        arguments: TokenStream,
        name: Symbol,
        span: FileSpan,
    ) -> Result<TokenStream, MacroExpansionError> {
        // Try each rule in order
        for rule in rules {
            if let Some(bindings) = self.try_match(&rule.matcher, &arguments) {
                // Match succeeded, expand with bindings
                return self.expand_with_bindings(&rule.expander, &bindings, span);
            }
        }

        // No rule matched
        Err(MacroExpansionError::NoRuleMatched {
            name,
            num_tokens: arguments.len(),
            span,
        })
    }

    /// Try to match a pattern against tokens
    fn try_match(&self, matcher: &MacroMatcher, tokens: &TokenStream) -> Option<Bindings> {
        let mut bindings = Bindings::default();
        let mut pos = 0;

        if self.match_pattern(matcher, &tokens.tokens, &mut pos, &mut bindings) {
            // Check if we consumed all tokens
            if pos == tokens.tokens.len() {
                Some(bindings)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Match a pattern against tokens
    #[allow(clippy::only_used_in_recursion, reason = "Will be used when full pattern matching is implemented")]
    fn match_pattern(
        &self,
        matcher: &MacroMatcher,
        tokens: &[Token],
        pos: &mut usize,
        bindings: &mut Bindings,
    ) -> bool {
        match matcher {
            MacroMatcher::Token(token) => {
                // Match literal token
                if *pos < tokens.len() && &tokens[*pos] == token {
                    *pos += 1;
                    true
                } else {
                    false
                }
            }
            MacroMatcher::MetaVar { name, kind } => {
                // Parse fragment
                if let Some(fragment) = self.parse_fragment(*kind, tokens, pos) {
                    bindings.insert(*name, Binding::Single(fragment));
                    true
                } else {
                    false
                }
            }
            MacroMatcher::Sequence {
                matchers,
                separator,
                kind,
            } => self.match_sequence(matchers, separator.as_ref(), *kind, tokens, pos, bindings),
            MacroMatcher::Group {
                delimiter,
                matchers,
            } => self.match_group(*delimiter, matchers, tokens, pos, bindings),
        }
    }

    /// Match a sequence pattern
    fn match_sequence(
        &self,
        matchers: &[MacroMatcher],
        separator: Option<&Token>,
        kind: SequenceKind,
        tokens: &[Token],
        pos: &mut usize,
        bindings: &mut Bindings,
    ) -> bool {
        let mut count = 0;
        let mut all_bindings = Vec::new();

        loop {
            let start_pos = *pos;
            let mut current_bindings = Bindings::default();

            // Try to match all matchers in sequence
            let mut matched = true;
            for matcher in matchers {
                if !self.match_pattern(matcher, tokens, pos, &mut current_bindings) {
                    matched = false;
                    break;
                }
            }

            if !matched {
                // Restore position
                *pos = start_pos;
                break;
            }

            count += 1;
            all_bindings.push(current_bindings);

            // Try to match separator
            if let Some(sep) = separator {
                if *pos < tokens.len() && &tokens[*pos] == sep {
                    *pos += 1;
                } else {
                    break;
                }
            } else if count > 0 {
                break;
            }
        }

        // Check if we matched the required number of times
        let matched = match kind {
            SequenceKind::ZeroOrMore => true,
            SequenceKind::OneOrMore => count >= 1,
            SequenceKind::Optional => count <= 1,
        };

        if matched {
            // Merge bindings
            for current_bindings in all_bindings {
                for (name, binding) in current_bindings {
                    bindings
                        .entry(name)
                        .or_insert_with(|| Binding::Multiple(Vec::new()));
                    if let Binding::Multiple(vec) = bindings.get_mut(&name).unwrap() {
                        if let Binding::Single(stream) = binding {
                            vec.push(stream);
                        }
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// Match a group pattern
    fn match_group(
        &self,
        delimiter: Delimiter,
        matchers: &[MacroMatcher],
        tokens: &[Token],
        pos: &mut usize,
        bindings: &mut Bindings,
    ) -> bool {
        if *pos >= tokens.len() {
            return false;
        }

        if let Token::Group { delim, stream } = &tokens[*pos] {
            if *delim == delimiter {
                // Match inside the group
                let mut inner_pos = 0;
                let mut matched = true;

                for matcher in matchers {
                    if !self.match_pattern(matcher, &stream.tokens, &mut inner_pos, bindings) {
                        matched = false;
                        break;
                    }
                }

                if matched && inner_pos == stream.tokens.len() {
                    *pos += 1;
                    return true;
                }
            }
        }

        false
    }

    /// Parse a fragment from tokens
    fn parse_fragment(&self, kind: FragmentKind, tokens: &[Token], pos: &mut usize) -> Option<TokenStream> {
        if *pos >= tokens.len() {
            return None;
        }

        match kind {
            FragmentKind::Ident => {
                // Parse identifier
                if let Token::Ident(_) = &tokens[*pos] {
                    let mut result = TokenStream::new();
                    result.push(tokens[*pos].clone());
                    *pos += 1;
                    Some(result)
                } else {
                    None
                }
            }
            FragmentKind::Expr => {
                // Simplified expression parsing: consume tokens until separator
                // This is a heuristic approach
                let start = *pos;
                let mut depth = 0;

                while *pos < tokens.len() {
                    match &tokens[*pos] {
                        Token::Group { .. } => {
                            depth += 1;
                            *pos += 1;
                        }
                        Token::Punct(',') | Token::Punct(';') if depth == 0 => {
                            break;
                        }
                        _ => {
                            *pos += 1;
                        }
                    }
                }

                if *pos > start {
                    let mut result = TokenStream::new();
                    for token in &tokens[start..*pos] {
                        result.push(token.clone());
                    }
                    Some(result)
                } else {
                    None
                }
            }
            FragmentKind::Ty => {
                // Simplified type parsing: similar to expr
                let start = *pos;
                let mut depth = 0;

                while *pos < tokens.len() {
                    match &tokens[*pos] {
                        Token::Group { .. } => {
                            depth += 1;
                            *pos += 1;
                        }
                        Token::Punct(',') | Token::Punct(';') if depth == 0 => {
                            break;
                        }
                        _ => {
                            *pos += 1;
                        }
                    }
                }

                if *pos > start {
                    let mut result = TokenStream::new();
                    for token in &tokens[start..*pos] {
                        result.push(token.clone());
                    }
                    Some(result)
                } else {
                    None
                }
            }
            FragmentKind::Tt => {
                // Token tree: just take one token
                let mut result = TokenStream::new();
                result.push(tokens[*pos].clone());
                *pos += 1;
                Some(result)
            }
            // For other fragment kinds, use simple heuristics
            _ => {
                let mut result = TokenStream::new();
                result.push(tokens[*pos].clone());
                *pos += 1;
                Some(result)
            }
        }
    }

    /// Expand template with bindings
    fn expand_with_bindings(
        &mut self,
        expander: &MacroExpander,
        bindings: &Bindings,
        span: FileSpan,
    ) -> Result<TokenStream, MacroExpansionError> {
        let mut result = TokenStream::new();
        self.expand_template(expander, bindings, &mut result, span)?;
        Ok(result)
    }

    /// Expand a template into a token stream
    fn expand_template(
        &mut self,
        expander: &MacroExpander,
        bindings: &Bindings,
        output: &mut TokenStream,
        span: FileSpan,
    ) -> Result<(), MacroExpansionError> {
        match expander {
            MacroExpander::Token(token) => {
                output.push(token.clone());
            }
            MacroExpander::Substitute(name) => {
                // Look up binding
                let binding = bindings.get(name).ok_or(MacroExpansionError::UnboundVariable {
                    name: *name,
                    span,
                })?;

                match binding {
                    Binding::Single(stream) => {
                        output.extend(stream.clone());
                    }
                    Binding::Multiple(_) => {
                        return Err(MacroExpansionError::InvalidSyntax {
                            message: "cannot substitute sequence binding outside of sequence".to_string(),
                            span,
                        });
                    }
                }
            }
            MacroExpander::Sequence {
                expanders,
                separator,
                kind: _,
            } => {
                // Find sequence bindings
                let mut sequence_bindings: Vec<&Vec<TokenStream>> = Vec::new();
                for exp in expanders {
                    if let MacroExpander::Substitute(name) = exp {
                        if let Some(Binding::Multiple(streams)) = bindings.get(name) {
                            sequence_bindings.push(streams);
                        }
                    }
                }

                if sequence_bindings.is_empty() {
                    return Ok(());
                }

                // Get the length of the first sequence
                let len = sequence_bindings[0].len();

                // Expand for each element
                for index in 0..len {
                    // Create bindings for this iteration
                    let mut iter_bindings = bindings.clone();
                    for exp in expanders {
                        if let MacroExpander::Substitute(name) = exp {
                            if let Some(Binding::Multiple(streams)) = bindings.get(name) {
                                if index < streams.len() {
                                    iter_bindings.insert(*name, Binding::Single(streams[index].clone()));
                                }
                            }
                        }
                    }

                    // Expand each expander
                    for exp in expanders {
                        self.expand_template(exp, &iter_bindings, output, span)?;
                    }

                    // Add separator if not last
                    if index < len - 1 {
                        if let Some(sep) = separator {
                            output.push(sep.clone());
                        }
                    }
                }
            }
            MacroExpander::Group {
                delimiter,
                expanders,
            } => {
                let mut inner = TokenStream::new();
                for exp in expanders {
                    self.expand_template(exp, bindings, &mut inner, span)?;
                }
                output.push(Token::Group {
                    delim: *delimiter,
                    stream: inner,
                });
            }
        }
        Ok(())
    }
}

impl Default for MacroExpansionContext {
    fn default() -> Self {
        Self::new(Interner::new())
    }
}
