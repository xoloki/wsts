# WSTS Security Policy

## Supported versions

Only the latest published release of the [`wsts`](https://crates.io/crates/wsts) crate receives security fixes. Older release lines are not maintained.

## Reporting a vulnerability

**Please do not open a public issue for a security vulnerability.**

Report it through [GitHub private vulnerability reporting](https://github.com/xoloki/wsts/security/advisories/new), which opens a private advisory visible only to you and the maintainer. This is the preferred channel: it keeps the report private, gives us a thread to triage in, and provides a private fork to develop a fix without disclosing the issue through a public branch.

If you would rather not use GitHub, or you want to agree on an encrypted channel before sending details, mail <xoloki@gmail.com>. Note that private vulnerability reporting is private to GitHub rather than end-to-end encrypted, so if the finding is sensitive enough that this matters, open with a short note and no detail, and we will arrange something else.

Expect an acknowledgement within a week. `WSTS` is maintained by one person, so please allow reasonable time for a fix before disclosing publicly.

## If you are reporting against sBTC

The [sBTC](https://github.com/stacks-sbtc/sbtc) project vendored `wsts` 14.0.0 into its own tree in March 2026 and the two implementations have since diverged in both directions. If the code you are looking at is `sbtc/wsts/`, the issue may not exist here and cannot be fixed here. Please report it to sBTC. See the Safety section of the README for what differs.

## How fixes are disclosed

When a report is resolved, we publish a GitHub Security Advisory and then open a companion advisory against [`rustsec/advisory-db`](https://github.com/rustsec/advisory-db). Both steps matter: `cargo audit` and `cargo deny` read the RustSec database rather than GitHub's, so a GHSA alone would leave Rust consumers unwarned. Reporters are credited unless they ask otherwise.

## Audit history

`WSTS` has been subject to independent security audits. Findings from those reviews are tracked in this repository under the `coinfabrik-audit` and `ottersec-audit` issue labels.
