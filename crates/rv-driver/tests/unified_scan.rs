use rv_driver::verify_rv_unified;
#[test]
fn scan_corpus() {
    let dir = format!("{}/../../examples/proofs", env!("CARGO_MANIFEST_DIR"));
    let mut names: Vec<String> = std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.ends_with(".rv")).collect();
    names.sort();
    let (mut pass, mut fail) = (0, 0);
    for n in &names {
        let src = std::fs::read_to_string(format!("{dir}/{n}")).unwrap();
        match verify_rv_unified(&src, None) {
            Ok(r) if r.all_verified() => { pass += 1; println!("PASS  {n}"); }
            Ok(r) => { fail += 1; println!("OPEN  {n}  {:?}", r.open); }
            Err(e) => { fail += 1; println!("FAIL  {n}  {}", e.lines().next().unwrap_or("")); }
        }
    }
    println!("\n=== {pass} pass, {fail} fail of {} ===", names.len());
}
