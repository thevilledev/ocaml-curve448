# Releasing

[Documentation](README.md) · [Project home](../README.md)

Preparing the source repository does not publish it to opam: a release
needs a tag, a public source archive and review by opam-repository
maintainers.

## Check the package

Use the [opam-repository policies](https://github.com/ocaml/opam-repository/blob/master/governance/policies/README.md)
and [submission guide](https://github.com/ocaml/opam-repository/blob/master/CONTRIBUTING.md)
as the source of truth.

1. Finish the changelog: its first heading is the version and the release
   date, such as `## 0.1.0 (2026-09-18)`. opam versions never carry a `v`
   prefix; the git tag may (see below).
2. Regenerate `curve448.opam` from `dune-project` and
   `curve448.opam.template`; check the maintainer, license, homepage,
   bug-report and source URLs and the `x-maintenance-intent` field, and
   review the diff.
3. Run the [development checks](../CONTRIBUTING.md) and
   [lower-bound test](compatibility.md#reproduce-the-lower-bound-test).
   Require the compiler, Dune and security CI jobs to pass.
4. In a disposable switch, run `opam install . --with-test --with-doc`.
   Also check installation without tests or docs in a fresh switch, to catch
   accidental dependencies on developer tools. Inspect the installed docs and
   third-party license notices.

The package keeps test dependencies behind `with-test` and odoc behind
`with-doc`, uses inclusive lower bounds, and avoids speculative upper bounds.
Formatting tools are development tools and are installed separately. Normal
package builds use vendored generated sources and fixtures without fetching
anything over the network.

`curve448.opam.template` declares `x-maintenance-intent: ["(latest)"]`: only
the latest release is maintained, as the opam-repository
[archiving policy](https://github.com/ocaml/opam-repository/blob/master/governance/policies/archiving.md)
describes. Dune has a field for this from language 3.18; the template
carries it because the project stays on language 3.6.

## Create and submit a release

Install `dune-release` and follow its
[release workflow](https://github.com/tarides/dune-release#readme). Build and
test the release archive itself, outside the checkout, before publishing it.
Include all source files, generated files, fixtures and license notices.

`dune-release` reads the version from the changelog heading, so
`dune-release tag` creates the tag `0.1.0`. For a tag with a `v` prefix,
such as `v0.1.0`, run `dune-release tag v0.1.0` and pass `--tag v0.1.0` to
`distrib`, `publish` and `opam`; dune-release drops the `v` when it derives
the opam version.

The opam-repository submission belongs at
`packages/curve448/curve448.<version>/opam`. Its `url` section must point to
the immutable, publicly downloadable release archive and contain a SHA-256
or stronger checksum. Do not submit a development branch, local pins or a
made-up archive URL. `dune-release` can prepare the archive and submission.

Never replace an already published source archive. Fix a broken release with
a new version. Check the current policies when submitting, and keep a human
maintainer responsible for the review discussion.
