# Local crates and solver dependencies

The following crates are maintained as ordinary directories in the rIC3
repository and are members of its Cargo workspace:

| Directory | Package | Imported source commit |
| --- | --- | --- |
| `aig-rs` | `aig` | [gipsyh/aig-rs@d47308c](https://github.com/gipsyh/aig-rs/commit/d47308c9d0d8da256be17a5218e46bfcca1cab61) |
| `bitwuzla-rs` | `smtif-bitwuzla` | [gipsyh/bitwuzla-rs@4dcb255](https://github.com/gipsyh/bitwuzla-rs/commit/4dcb255897e4226c0e3c996e548ba6e9aa7d7dc2) |
| `btor-rs` | `btor` | [gipsyh/btor-rs@4eaa050](https://github.com/gipsyh/btor-rs/commit/4eaa050a4a207f73a7dabf9fce214dced553154d) |
| `cadical-rs` | `satif-cadical` | [gipsyh/cadical-rs@7c8bf71](https://github.com/gipsyh/cadical-rs/commit/7c8bf71a3b73985ea81430e1902408ab310dd894) |
| `giputils` | `giputils` | [gipsyh/giputils@d763caa](https://github.com/gipsyh/giputils/commit/d763caa09d2d2234b6fec767345994030ba3eac3) |
| `kissat-rs` | `satif-kissat` | [gipsyh/kissat-rs@2f5c7ff](https://github.com/gipsyh/kissat-rs/commit/2f5c7ff6626456f8b402ca7c6319e7814abc3a85) |
| `logicrs` | `logicrs` | [gipsyh/logicrs@1c0a531](https://github.com/gipsyh/logicrs/commit/1c0a531031eba3235980ede9397dda929d0788e0) |

These are source snapshots of the recorded commits. Their existing crate
names, versions, and MIT licenses are retained; earlier history remains in
the linked repositories. Make future changes to these crates in rIC3.

The workspace shares the root `Cargo.lock`, build output directory, and
local dependency declarations in `[workspace.dependencies]`. Root commands
select rIC3 by default; use `--workspace` to check or test all eight packages.

The native solver sources remain submodules, registered directly in the root
`.gitmodules`:

- `cadical-rs/cadical`
- `kissat-rs/kissat`
- `bitwuzla-rs/bitwuzla`

Initialize them with `git submodule update --init --recursive`. A wrapper's
build script also initializes its own missing solver submodule when needed,
without fetching other solvers or benchmarks. Bitwuzla uses the system library
by default and only builds its native submodule with the `vendor` feature.
Its native solver tests run when the library is available; otherwise a test
checks the diagnostic from the stub implementation. The benchmark repository
at `examples/fvbench` also remains a submodule.

Each local crate can still be published separately. Workspace inheritance is
resolved when Cargo packages a crate; registry consumers use the declared
dependency versions rather than this checkout. Publish updated dependencies
and adjust version requirements before publishing packages that use new APIs.

The root Dependabot configuration covers the workspace. The optional C
wrapper in `giputils/cpp` explicitly builds its Rust archive into
`giputils/target` so its CMake library path stays independent of the shared
workspace target directory.
