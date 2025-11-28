import Mathlib.Tactic

section Lewis

variable {indiv : Type*}
variable (A φ : Prop)

variable {R : indiv → Prop → Prop}
variable {Ind : Prop → indiv → Prop → Prop}

variable (A1 : ∀ {i : indiv} {p : Prop}, Ind A i p → R i A → R i p)

variable (A6 : ∀ {i j : indiv} {u : Prop}, Ind A i (R j A) ∧ R i (Ind A j u) → Ind A i (R j u))

variable (C1 : ∀ i : indiv, R i A)

variable (C2 : ∀ i j : indiv, Ind A i (R j A))

variable (C3 : ∀ i : indiv, Ind A i φ)

variable (C4 :  ∀ {i j : indiv} {u : Prop}, Ind A i u → R i (Ind A j u))

include A1 A6 C1 C2 C3 C4

omit A6 C2 C4 in
lemma L1
  (i : indiv) : R i φ := by
  have h₁ : R i A := C1 i
  have h₂ : Ind A i φ := C3 i
  exact A1 h₂ h₁

omit A6 C2 C4 in
lemma L1_aesop
  (i : indiv) : R i φ := by aesop

lemma L2
  (i j : indiv) : R i (R j φ) := by
  have h₁ : Ind A i φ := C3 i
  have h₂ : R i (Ind A j φ) := C4 h₁
  have h₃ : Ind A i (R j φ) := A6 ⟨C2 i j, h₂⟩
  exact A1 h₃ (C1 i)

omit A6 C4 in
lemma L2_aesop
  (i j : indiv) : R i (R j φ) := by aesop

lemma L3
  (i j k : indiv) :  R i (R j (R k φ)) := by
  have h₁ : Ind A i φ := C3 i
  have h₂ : R i (Ind A k φ) := C4 h₁
  have h₃ : Ind A i (R k φ) := A6 ⟨C2 i k, h₂⟩
  have h₄ : R i (Ind A j (R k φ)) := C4 h₃
  have h₅ : Ind A i (R j (R k φ)) := A6 ⟨C2 i j, h₄⟩
  exact A1 h₅ (C1 i)

lemma L3_aesop
  (i j k : indiv) : R i (R j (R k φ)) := by aesop

lemma L4
  (i j k l : indiv) : R i (R j (R k (R l φ))) := by
  have h₁ : Ind A i φ := C3 i
  have h₂ : R i (Ind A l φ) := C4 h₁
  have h₃ : Ind A i (R l φ) := A6 ⟨C2 i l, h₂⟩
  have h₄ : R i (Ind A k (R l φ)) := C4 h₃
  have h₅ : Ind A i (R k (R l φ)) := A6 ⟨C2 i k, h₄⟩
  have h₆ : R i (Ind A j (R k (R l φ))) := C4 h₅
  have h₇ : Ind A i (R j (R k (R l φ))) := A6 ⟨C2 i j, h₆⟩
  exact A1 h₇ (C1 i)

lemma L4_aesop
  (i j k l : indiv) : R i (R j (R k (R l φ))) := by aesop

inductive RC (φ : Prop) : Prop → Prop where
  | base : RC φ φ
  | step {u : Prop} (j : indiv) (hu : RC φ u) : RC φ (R j u)

omit A1 C1 in
lemma rc_implies_indication
  {i : indiv} {q : Prop} (h : @RC indiv R φ q) : Ind A i q := by
  induction h with
  | base =>
      exact C3 i
  | @step v j _ ih =>
      have h₁ : R i (Ind A j v) := C4 ih
      have h₂ : Ind A i (R j v) := A6 ⟨C2 i j, h₁⟩
      exact h₂

lemma everyone_reason_of_rc
  (hp : @RC indiv R φ p) : ∀ i : indiv, R i p := by
  intro i
  have hInd : Ind A i p := rc_implies_indication A φ A6 C2 C3 C4 hp
  exact A1 hInd (C1 i)

end Lewis
