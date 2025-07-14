# Raven

[![codecov](https://codecov.io/gh/BigBadE/Raven-Rewrite/graph/badge.svg?token=FeExMvT7w1)](https://codecov.io/gh/BigBadE/Raven-Rewrite)
[![DeepSource](https://app.deepsource.com/gh/BigBadE/Raven-Rewrite.svg/?label=active+issues&show_trend=true&token=Q4sospH9xYMKaXCKqCWahjxG)](https://app.deepsource.com/gh/BigBadE/Raven-Rewrite/)
[![CodeScene Average Code Health](https://codescene.io/projects/65635/status-badges/average-code-health)](https://codescene.io/projects/65635)

# Building

The build script will handle installing all dependencies needed, but you need to manually add Cranelift to your system:

rustup component add rustc-codegen-cranelift-preview --toolchain nightly

You will also need the latest C++ build tools, which can be downloaded with Visual Studio Installer.

# Common errors

## Linker errors

- Make sure you have the latest version of the C++ build tools installed.
- Run cargo clean