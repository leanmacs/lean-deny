/- A block comment that mentions
import Core.Fake -/
module -- the module system is on

public import Core.Types import all Core.Impl
public meta import Core.Macros
-- a comment between directives
meta
  import Base
