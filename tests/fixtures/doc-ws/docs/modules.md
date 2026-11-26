# Doc modules

The doc-modules fixtures' module map: one section per case.

## Exact

| Module | File | Notes |
| --- | --- | --- |
| `Doc.A` | `Doc/A.lean` | uses `Nat.succ` |
| `Doc.B` | `lean/Doc/` | see `Doc.A` again |

### Deeper

A deeper subsection is part of the section: `Doc.B` again.

## Missing

- `Doc.A`

## Extra

- `Doc.A`, `Doc.B`
- `Doc.Gone`
- `Nat.succ` has no prefix, so it is not listed.

```lean
-- `Doc.Fenced` is in a code block, so it is not listed.
```

## Both

- `Doc.A`
- `Doc.Gone`

## Twice

## Twice
