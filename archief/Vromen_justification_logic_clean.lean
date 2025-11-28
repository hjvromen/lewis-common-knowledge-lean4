import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic

namespace JustificationLogic

structure JustificationFrame (individual reason : Type*) [Mul reason] where
  reasonBelief : reason → individual → Prop → Prop

variable {individual reason : Type*} [Mul reason]
variable (frame : JustificationFrame individual reason)

def R (rb : reason → individual → Prop → Prop) (i : individual) (φ : Prop) : Prop :=
  ∃ r, rb r i φ

variable {rb: reason → individual → Prop → Prop}

def Ind (rb : reason → individual → Prop → Prop) (φ : Prop) (i : individual) (ψ : Prop) : Prop :=
  R rb i (φ → ψ)

axiom conjConst : reason
axiom transConst : reason
axiom distConst : reason

axiom AR {rb : reason → individual → Prop → Prop} :
  ∀ {s t : reason} {i : individual} {α β : Prop},
  rb s i (α → β) → rb t i α → rb (s * t) i β

axiom T1 {rb : reason → individual → Prop → Prop} :
  ∀ {i : individual} {α β : Prop}, rb conjConst i (α → β → (α ∧ β))

axiom T2 {rb : reason → individual → Prop → Prop} :
  ∀ {i : individual} {α β γ : Prop}, rb transConst i (((α → β) ∧ (β → γ)) → (α → γ))

axiom T3 {rb : reason → individual → Prop → Prop} :
  ∀ {i j : individual} {α β : Prop},
  rb distConst i (R rb j (α → β) → (R rb j α → R rb j β))

lemma E1 {rb : reason → individual → Prop → Prop} :
    ∀ {i : individual} {α β : Prop}, R rb i (α → β) → R rb i α → R rb i β := by
  intro i α β h1 h2
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  use s * t
  exact AR hs ht

lemma L1 {rb : reason → individual → Prop → Prop} :
    ∀ {i : individual} {α β : Prop}, R rb i α → R rb i β → R rb i (α ∧ β) := by
  intro i α β h1 h2
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have h3 : rb (conjConst * s) i (β → (α ∧ β)) := by
    have h4 : rb conjConst i (α → (β → (α ∧ β))) := T1
    exact AR h4 hs
  use conjConst * s * t
  exact AR h3 ht

lemma E2 {rb : reason → individual → Prop → Prop} :
    ∀ {i : individual} {α β γ : Prop},
    R rb i (α → β) → R rb i (β → γ) → R rb i (α → γ) := by
  intro i α β γ h1 h2
  have h3 : R rb i ((α → β) ∧ (β → γ)) := L1 h1 h2
  obtain ⟨s, hs⟩ := h3
  use transConst * s
  exact AR T2 hs

lemma E3 {rb : reason → individual → Prop → Prop} :
    ∀ {i j : individual} {α β : Prop},
    R rb i (R rb j (α → β)) → R rb i (R rb j α → R rb j β) := by
  intro i j α β h1
  obtain ⟨s, hs⟩ := h1
  use distConst * s
  exact AR T3 hs

section LewisAxioms

variable (A : Prop)

lemma A1 {rb : reason → individual → Prop → Prop} :
    ∀ {i : individual} {α : Prop}, Ind rb A i α → R rb i A → R rb i α := by
  intro i α h1 h2
  obtain ⟨t, ht⟩ := h2
  obtain ⟨s, hs⟩ := h1
  use s * t
  exact AR hs ht

lemma A1_alternative_proof {rb : reason → individual → Prop → Prop} :
    ∀ {i : individual} {α : Prop}, Ind rb A i α → R rb i A → R rb i α :=
  fun h1 h2 => E1 h1 h2

lemma A6 {rb : reason → individual → Prop → Prop} :
    ∀ α {i j : individual},
    Ind rb A i (R rb j A) →
    R rb i (Ind rb A j α) →
    Ind rb A i (R rb j α) := by
  intro p i j h1 h2
  have h3 : R rb i (R rb j A → R rb j p) := E3 h2
  have h4 : R rb i (A → R rb j p) := E2 h1 h3
  exact h4

end LewisAxioms

inductive Gclosure (φ : Prop) : Prop → Prop
  | base : Gclosure φ φ
  | step (p : Prop) (i : individual) : Gclosure φ p → Gclosure φ (R rb i p)

theorem Lewis  (A φ : Prop)
    (C1 : ∀ i, R rb i A)
    (C2 : ∀ i j, Ind rb A i (R rb j A))
    (C3 : ∀ i, Ind rb A i φ)
    (C4 : ∀ α i j, Ind rb A i α → R rb i (Ind rb A j α))
    (h7 : @Gclosure individual reason rb φ p) :
    ∀ i, R rb i p := by
  intro i
  have h1 : Ind rb A i p := by
    induction h7 with
    | base =>
        exact C3 _
    | step u j hu ih =>
        have h3 : R rb i (Ind rb A j u) := C4 u _ _ ih
        have h4 : R rb i (Ind rb A j u) → Ind rb A i (R rb j u) :=
          A6 A u (C2 _ _)
        have h5 : Ind rb A i (R rb j u) := h4 h3
        exact h5
  exact A1 A h1 (C1 _)

end JustificationLogic
