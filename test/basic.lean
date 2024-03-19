def someVal : Sum Nat Int := .inl 27

inductive Tree
| leaf
| branch (s : Tree) (s : Tree)

@[simp]
def someTree : Tree :=
  .branch
    (.branch .leaf .leaf)
    (.leaf)
