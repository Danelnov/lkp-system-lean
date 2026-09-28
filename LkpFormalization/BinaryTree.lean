inductive BNTree (α : Type u) where
  | leaf
  | node (left : BNTree α) (value : α) (right : BNTree α)
  deriving Repr, DecidableEq, Inhabited


namespace BNTree

variable {α}

instance : Coe α (BNTree α) := ⟨fun v => node leaf v leaf⟩

def insert_right (T : BNTree α) (value : α) : BNTree α :=
  node leaf value T

def insert_left (T : BNTree α) (value : α) : BNTree α :=
  node T value leaf

end BNTree
