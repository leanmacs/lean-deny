# Doc packages

The doc-packages fixtures' package tables: one section per case.

## Agrees

- A list item holds a nested table, which disagrees but is not read:

  | Package | Layer | Requires |
  |---|---|---|
  | `impl` | interface | `gone` |

A top-level table without the Requires column is not the package table:

| Package | Layer |
|---|---|
| `gone` | nowhere |

| Package | Layer | Requires | Notes |
| :--- | --- | ---: | --- |
| `impl` | implementation | `api` | the rows need not be in order |
| `api` | `interface` | none | a layer may be in backticks |

```text
| Package | Layer | Requires |
|---|---|---|
| `gone` | nowhere | none |
```

## Broken

| Package | Layer | Requires |
|---|---|---|
| `gone` | interface | none |
| `api` | implementation | `impl` |

## No requires

| Package | Layer |
|---|---|
| `api` | interface |
| `impl` | implementation |
