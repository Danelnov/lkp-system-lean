import LkpFormalization.Basic
import LkpFormalization.Data
import TypstInfoview
import LkpFormalization.Tactic

open LkpFormalization
open BNTree Sequent PropForm

namespace Gentzen

def ax (s : Sequent) : Option (BNTree Sequent) :=
  if s.has_common_elements then
    node leaf s leaf
  else
    none

def conj_left (i : Nat) : BNTree (Sequent) → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Γ.splitAt i with
    | (Γ₁, A::B::Γ₂) =>
      node T (Γ₁ ++ (A ∧ₚ B)::Γ₂, Δ) leaf
    | _ => none
  | _ => none

def conj_right (i : Nat) : BNTree (Sequent) → BNTree (Sequent) → Option (BNTree Sequent)
  | T₁@(node _ (Γ, Δ) _), T₂@(node _ (Γ', Δ') _) =>
    match Δ.splitAt i, Δ'.splitAt i with
    | (Δ₁, A::Δ₂), (Δ'₁, B::Δ'₂) =>
      if Γ = Γ' ∧ Δ₁ = Δ'₁ ∧ Δ₂ = Δ'₂ then
        node T₁ (Γ, Δ₁ ++ (A ∧ₚ B)::Δ₂) T₂
      else
        none
    | _, _ => none
  | _, _ => none

def disj_left (i : Nat) : BNTree (Sequent) → BNTree (Sequent) → Option (BNTree Sequent)
  | T₁@(node _ (Γ, Δ) _), T₂@(node _ (Γ', Δ') _) =>
    match Γ.splitAt i, Γ'.splitAt i with
    | (Γ₁, A::Γ₂), (Γ'₁, B::Γ'₂) =>
      if Δ = Δ' ∧ Γ₁ = Γ'₁ ∧ Γ₂ = Γ'₂ then
        node T₁ (Γ₁ ++ (A ∨ₚ B)::Γ₂, Δ) T₂
      else
        none
    | _, _ => none
  | _, _ => none

def disj_right (i : Nat) : BNTree (Sequent) → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Δ.splitAt i with
    | (Δ₁, A::B::Δ₂) =>
      node T (Γ, Δ₁ ++ (A ∨ₚ B)::Δ₂) leaf
    | _ => none
  | _ => none

def impl_left (i : Nat) : BNTree (Sequent) → BNTree (Sequent) → Option (BNTree Sequent)
  | T₁@(node _ (Γ, A::Δ) _), T₂@(node _ (B::Γ', Δ') _) =>
    if Γ = Γ' ∧ Δ = Δ' then
      let (Γ₁, Γ₂) := Γ.splitAt i
      node T₁ (Γ₁ ++ (A ⊃ₚ B)::Γ₂, Δ) T₂
    else
      none
  | _, _ => none

def impl_right (i : Nat) : BNTree (Sequent) → Option (BNTree Sequent)
  | T@(node _ (A::Γ, B::Δ) _ ) =>
    let (Δ₁, Δ₂) := Δ.splitAt i
    node T (Γ, Δ₁ ++ (A ⊃ₚ B)::Δ₂) leaf
  | _ => none

def neg_left (i : Nat) : BNTree (Sequent) → Option (BNTree Sequent)
  | T@(node _ (Γ, A::Δ) _ ) =>
    let (Γ₁, Γ₂) := Γ.splitAt i
    node T (Γ₁ ++ (¬ₚ A)::Γ₂, Δ) leaf
  | _ => none

def neg_right (i : Nat) : BNTree (Sequent) → Option (BNTree Sequent)
  | T@(node _ (A::Γ, Δ) _ ) =>
    let (Δ₁, Δ₂) := Δ.splitAt i
    node T (Γ, Δ₁ ++ (¬ₚ A)::Δ₂) leaf
  | _ => none

end Gentzen

open Gentzen

def contrareci : BNTree Sequent :=
  lk_derive [seq| ⊢ (P ⊃ Q) ⊃ (¬Q ⊃ ¬P)] by
    apply_rule (impl_right 0) (P ⊃ Q ⊢ ¬Q ⊃ ¬P)
    left
    apply_rule (impl_right 1) (¬Q, P ⊃ Q ⊢ ¬P)
    left
    apply_rule (neg_left 0) (P ⊃ Q ⊢ Q, ¬P)
    left
    apply_rule (neg_right 1) (P, P ⊃ Q ⊢ Q)
    left
    apply_rule (impl_left 1) (P ⊢ P, Q) (Q, P ⊢ Q)
    left
    apply_rule (ax [seq| P ⊢ P, Q])
    next
    apply_rule (ax [seq| Q, P ⊢ Q])
