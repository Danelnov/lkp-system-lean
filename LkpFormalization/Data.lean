import TypstInfoview

namespace LkpFormalization

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

def BNTree.toTypstAux [ToTypst α] : BNTree α → String
  | .leaf => ""
  | .node l v r =>
    let ltyp := match l with
      | leaf => ""
      | _     => s!"  {BNTree.toTypstAux l},\n"

    let rtyp := match r with
      | leaf => ""
      | _     => s!"  {BNTree.toTypstAux r},\n"

    if ltyp == "" && rtyp == "" then
      s!"{toTypst v}"
    else
      s!"rule(\n{ltyp}{rtyp}  {toTypst v}\n)"

instance [ToTypst α] : ToTypst (BNTree α) where
  toTypst := fun t => "prooftree(\n  " ++ (BNTree.toTypstAux t) ++ "\n)"

end BNTree

inductive PTree (α : Type) where
  | empty : PTree α
  | goal (value : α) : PTree α
  | node (left : PTree α) (value : α) (right : PTree α)
  deriving Inhabited, Repr

inductive Ctx (α : Type) where
  | top : Ctx α
  | inLeft : Ctx α → α → PTree α → Ctx α
  | inRight : PTree α → α → Ctx α → Ctx α
  deriving Inhabited

structure Zipper (α : Type) where
  focus : PTree α
  ctx   : Ctx α

section

variable {α : Type}

def PTree.goals : PTree α → List α
  | empty       => []
  | goal a      => [a]
  | node l _ r  => l.goals ++ r.goals

def Ctx.plug : Ctx α → PTree α → PTree α
  | top, t            => t
  | inLeft c a r, t   => c.plug (.node t a r)
  | inRight l a c, t  => c.plug (.node l a t)

namespace Zipper

def ofTree (t : PTree α) : Zipper α := ⟨t, .top⟩
def toTree (z : Zipper α) : PTree α := z.ctx.plug z.focus
def goals (z : Zipper α) : List α := z.toTree.goals

def up? (z : Zipper α) : Option (Zipper α) :=
  match z.ctx with
  | .top => none
  | .inLeft c a r => some ⟨.node z.focus a r, c⟩
  | .inRight l a c => some ⟨.node l a z.focus, c⟩

def firstGoalIn : PTree α → Ctx α → Option (Zipper α)
  | .empty, _ => none
  | .goal a, c => some ⟨.goal a, c⟩
  | .node l a r, c =>
    match firstGoalIn l (.inLeft c a r) with
    | some z => some z
    | none => firstGoalIn r (.inRight l a c)

def goLeft? (z : Zipper α) : Option (Zipper α) :=
  match z.focus with
  | .node l a r => firstGoalIn l (.inLeft z.ctx a r)
  | _ => none

def goRight? (z : Zipper α) : Option (Zipper α) :=
  match z.focus with
  | .node l a r => firstGoalIn r (.inRight l a z.ctx)
  | _ => none

def nextIn : PTree α → Ctx α → Option (Zipper α)
  | _, .top => none
  | t, .inLeft c a r =>
    match firstGoalIn r (.inRight t a c) with
    | some z => some z
    | none => nextIn (.node t a r) c
  | t, .inRight l a c => nextIn (.node l a t) c

def nextGoal? (z : Zipper α) : Option (Zipper α) := nextIn z.focus z.ctx

end Zipper
end

end LkpFormalization
