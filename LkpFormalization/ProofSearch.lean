import LkpFormalization.Basic
import LkpFormalization.Data
import LkpFormalization.Notation
import TypstInfoview

open LkpFormalization
open PTree PropForm

namespace LkpFormalization

namespace Sequent

def ax (s : Sequent) : Option (PTree Sequent) :=
  if s.hasCommonElements then
    node empty s empty
  else
    none

def conj_left (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Γ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | conj A B =>
      some (node (goal (Λ₁ ++ A::B::Λ₂, Δ)) s empty)
    | _ => none
  | _ => none

def conj_right (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Δ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | conj A B =>
      some (node (goal (Γ, Λ₁ ++ A::Λ₂)) s (goal (Γ, Λ₁ ++ B::Λ₂)))
    | _ => none
  | _ => none

def disj_left (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Γ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | disj A B =>
      some (node (goal (Λ₁ ++ A::Λ₂, Δ)) s (goal (Λ₁ ++ B::Λ₂, Δ)))
    | _ => none
  | _ => none

def disj_right (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Δ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | disj A B =>
      some (node (goal (Γ, Λ₁ ++ A::B::Λ₂)) s empty)
    | _ => none
  | _ => none

def impl_left (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Γ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | impl A B =>
      some (node (goal (Λ₁ ++ Λ₂, A::Δ)) s (goal (B::Λ₁ ++ Λ₂, Δ)))
    | _ => none
  | _ => none

def impl_right (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Δ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | impl A B =>
      some (node (goal (A::Γ, B::Λ₁ ++ Λ₂)) s empty)
    | _ => none
  | _ => none

def neg_left (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Γ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | neg A =>
      some (node (goal (Λ₁ ++ Λ₂, A::Δ)) s empty)
    | _ => none
  | _ => none

def neg_right (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  let (Γ, Δ) := s
  match Δ.splitAt i with
  | (Λ₁, P::Λ₂) =>
    match P with
    | neg A =>
      some (node (goal (A::Γ, Λ₁ ++ Λ₂)) s empty)
    | _ => none
  | _ => none

def apply_left (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  if let some t := ax s then t
  else match s.1.splitAt i with
  | (_, P::_) =>
    match P with
    | conj _ _  => s.conj_left i
    | disj _ _  => s.disj_left i
    | impl _ _  => s.impl_left i
    | neg _     => s.neg_left i
    | _         => none
  | _ => none

def apply_right (s : Sequent) (i : Nat) : Option (PTree Sequent) :=
  if let some t := ax s then t
  else match s.2.splitAt i with
  | (_, P::_) =>
    match P with
    | conj _ _  => s.conj_right i
    | disj _ _  => s.disj_right i
    | impl _ _  => s.impl_right i
    | neg _     => s.neg_right i
    | _         => none
  | _ => none

def leftNonBranching (s : Sequent) : Option (PTree Sequent) :=
  if let some i := s.1.findIdx? nonBranching then
    s.apply_left i
  else none
where
  nonBranching : PropForm → Bool
  | var _ | disj _ _ | impl _ _   => false
  | _                             => true

def rightNonBranching (s : Sequent) : Option (PTree Sequent) :=
  if let some i := s.2.findIdx? nonBranching then
    s.apply_right i
  else none
where
  nonBranching : PropForm → Bool
  | var _ | conj _ _  => false
  | _                 => true

partial def treeNonBranchingTail (s : Sequent) (t : PTree Sequent) : Option (PTree Sequent) :=
  match s.leftNonBranching with
  | some T@(node (goal s') _ _) => s'.treeNonBranchingTail (t.insertLeft T)
  | _ =>
    match s.rightNonBranching with
    | some T@(node (goal s') _ _) => s'.treeNonBranchingTail (t.insertLeft T)
    | _ => t

end Sequent

end LkpFormalization

def xs : Sequent := [seq| A, ¬B, A∧B ⊢ A ⊃ B]

set_option typst.preamble "#import \"@preview/curryst:0.6.0\": rule, prooftree, rule-set" in
#typst (xs.treeNonBranchingTail (empty)).get!.toBNTree
