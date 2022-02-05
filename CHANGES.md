## 0.0.2
- fix: `return` nodes were always re-evaluated, along pending callbacks...
- optim: unbox some types
- optim: do not produce human-readable tags unless in `debug` mode
- optim: in nodes `bind m f`, do not call `f` unless `m` has been invalidated
- new: expose `undo` function, allowing to backtrack at most one `Var.set` followed by a `get` (experimental)
- new: expose infix `let+` and `map+`
- new: expose `tracking` variables
- new: `map_array` node

## 0.0.1
- First release
