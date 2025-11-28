import Mathlib.Tactic
import Mathlib.Logic.Relation

namespace Sillari

structure MultiAgentFrame (Agent : Type*) where
  World : Type*
  rel : Agent → World → World → Prop

variable {Agent : Type} {frame : MultiAgentFrame Agent}
variable {φ : frame.World → Prop}

def modal_imp (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w → ψ w
infixr:90 " ⟶ₘ " => modal_imp

def modal_conj (φ ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => φ w ∧ ψ w
infixr:70 " ∧ₘ " => modal_conj

def valid (φ : frame.World → Prop) : Prop := ∀ w, φ w
notation "⊢ " φ => valid φ

def R (i : Agent) (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀ v, frame.rel i w v → φ v

def Rg (φ : frame.World → Prop) : frame.World → Prop :=
    fun w => ∀ i, R i φ w

def Ind (i : Agent) (φ : frame.World → Prop) (ψ : frame.World → Prop) : frame.World → Prop :=
  fun w => R i φ w ∧ (φ w → ψ w)

def connected (w1 w2 : frame.World) : Prop :=
  ∃ i, frame.rel i w1 w2

inductive trcl (r : frame.World → frame.World → Prop) : frame.World → frame.World → Prop
| base {x y} : r x y → trcl r x y
| step {x y z} : r x y → trcl r y z → trcl r x z

lemma trcl.head {r : frame.World → frame.World → Prop}
    (h : r x y) (p : trcl r y z) : trcl r x z :=
  trcl.step h p

def path_cons {i : Agent} {x y : frame.World} (h : frame.rel i x y) :
    ∀ {z : frame.World}, trcl connected y z → trcl connected x z :=
  fun p => trcl.head ⟨i, h⟩ p

def CRB (ψ : frame.World → Prop) (s : frame.World) : Prop :=
  ∀ w, trcl (connected : frame.World → frame.World → Prop) s w → ψ w

lemma CRB.counterexample {ψ : frame.World → Prop} {s w : frame.World}
    (hsw : trcl (connected : frame.World → frame.World → Prop) s w) (hnot : ¬ ψ w) :
    ¬ CRB ψ s := by
  intro hCR
  exact hnot (hCR w hsw)

lemma not_CRB_iff_exists {ψ : frame.World → Prop} {s : frame.World} :
    (¬ CRB ψ s) ↔ ∃ w, trcl (connected : frame.World → frame.World → Prop) s w ∧ ¬ ψ w := by
  classical
  unfold CRB
  aesop

def three_worlds : frame.World → frame.World → frame.World → Prop :=
  fun w1 w2 w3 => w2 ≠ w1 ∧ w3 ≠ w2 ∧ w3 ≠ w1

def two_worlds : frame.World → frame.World → Prop :=
  fun w1 w2 => w1 ≠ w2

def two_agents : Agent → Agent → Prop :=
  fun i1 i2 => i1 ≠ i2 ∧ ∀ i, i = i1 ∨ i = i2

lemma trcl_trans {r : frame.World → frame.World → Prop} {x y z : frame.World} :
    trcl r x y → trcl r y z → trcl r x z := by
  intro hxy hyz
  induction hxy with
  | base hxy => exact trcl.step hxy hyz
  | step hxy _ ih => exact trcl.step hxy (ih hyz)

lemma trcl_single {r : frame.World → frame.World → Prop} {x y : frame.World}
    (h : r x y) : trcl r x y :=
  trcl.base h

lemma R_mono {i : Agent} {φ ψ : frame.World → Prop} {w : frame.World}
    (h : ∀ v, φ v → ψ v) : R i φ w → R i ψ w := by
  intro hRφ v hrel
  exact h v (hRφ v hrel)

lemma Rg_mono {φ ψ : frame.World → Prop} {w : frame.World}
    (h : ∀ v, φ v → ψ v) : Rg φ w → Rg ψ w := by
  intro hRgφ i
  exact R_mono h (hRgφ i)

lemma CRB_mono {φ ψ : frame.World → Prop} {s : frame.World}
    (h : ∀ v, φ v → ψ v) : CRB φ s → CRB ψ s := by
  intro hCRBφ v hv
  exact h v (hCRBφ v hv)

lemma CRB_alt {ψ : frame.World → Prop} {s : frame.World} :
    CRB ψ s ↔ ∀ w, trcl connected s w → ψ w := by
  rfl

lemma B1 : ∀ w, R i φ w → R i (φ ⟶ₘ ψ) w → R i ψ w := by
  intros v h1 h2 u h3
  aesop

lemma B2 : ∀ w, R i φ w → (φ ⟶ₘ ψ) w → Ind i φ ψ w := by
  intro w h1 h2
  constructor
  { assumption }
  { aesop}

lemma B3_fails
  (h2a : ¬ frame.rel i s s)
  (h2b : frame.rel i s t) :
    ¬ (∀ w (φ ψ : frame.World → Prop), R i φ w → Ind i φ ψ w → R i ψ w) := by
  let ψ := fun w => w ≠ t
  let φ := fun w => w ≠ s
  push_neg
  have h4 : R i φ s := by
    intro v hv
    aesop
  have h5 : Ind i φ ψ s := by
    rw [Ind]
    aesop
  have h6 : ¬ R i ψ s := by aesop
  refine ⟨s, φ, ψ, h4, h5, h6⟩

lemma B4 : ∀ w, Ind i φ γ w → Ind i γ ψ w → Ind i φ ψ w := by
  intro w h1 h2
  constructor
  { exact h1.1 }
  { have h4 : φ w → γ w := h1.2
    have h5 : γ w → ψ w := h2.2
    intro hw
    exact h5 (h4 hw) }

lemma B5 : (⊢ φ) → (⊢ (φ ⟶ₘ ψ)) → (⊢ ψ) := by
  intro h1 h2 w
  aesop

lemma B6 : (⊢ φ) → (⊢ R i φ) := by
  intro h1 u v
  aesop

lemma B10 : ⊢ CRB φ ⟶ₘ Rg (φ ∧ₘ CRB φ) := by
  intro s hCR i t hst
  constructor
  · exact hCR t (trcl_single ⟨i, hst⟩)
  · intro w htw
    have hst_path : trcl connected s t := trcl_single ⟨i, hst⟩
    exact hCR w (trcl_trans hst_path htw)

lemma B11 : (⊢ φ ⟶ₘ Rg (ψ ∧ₘ φ)) → ⊢ (φ ⟶ₘ CRB ψ) := by
  intro hvalid s hφs
  have propagate :
      ∀ {x y}, φ x →
        trcl (connected : frame.World → frame.World → Prop) x y →
        (ψ y ∧ φ y) := by
    intro x y hφx hxy
    induction hxy with
    | base hconn =>
        rename_i x y
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        exact hRg j y hj
    | step hconn hrest ih =>
        rename_i x y z
        rcases hconn with ⟨j, hj⟩
        have hRg : Rg (ψ ∧ₘ φ) x := (hvalid x) hφx
        have hy : (ψ ∧ₘ φ) y := hRg j y hj
        exact ih hy.2
  intro w hsw
  exact (propagate hφs hsw).1

lemma C4_fails
  (h2a : ¬ frame.rel i s s)
  (h2b : frame.rel i s t) :
    ¬ ∀ w (φ ψ : frame.World → Prop), (Ind i φ ψ w → R i (Ind j φ ψ) w) := by
  let φ := fun _ : frame.World => True
  let ψ := fun w : frame.World => w = s
  push_neg
  have h3 : Ind i φ ψ s := by
    constructor
    { intro w _; aesop }
    { aesop }
  have h3a : ¬ R i (Ind j φ ψ) s := by
    rw [R]
    push_neg
    use t
    constructor
    { exact h2b }
    { intro hn
      have hphi : φ t := by aesop
      have hp : ψ t := hn.2 hphi
      have h3b : ¬ ψ t := by aesop
      aesop }
  use s, φ, ψ

section LewisTheoremOption1

lemma Lewis_fails_1i
   (h3w : three_worlds s u v)
    (hrel :
      frame.rel =
        (fun (_ : Agent) (w1 w2 : frame.World) =>
          (w1 = s ∧ w2 = u) ∨ (w1 = u ∧ w2 = v)))
     : ∃ φ, R i1 φ s ∧ Ind i1 (R i1 φ) (R i1 (R i1 φ)) s ∧
      Ind i1 (R i1 φ) (R i1 (fun w => w = u)) s ∧ ¬ CRB (fun w => w = u) s := by
  obtain ⟨hsu, hvu, hvs⟩ : u ≠ s ∧ v ≠ u ∧ v ≠ s := by
    simpa [three_worlds] using h3w
  let φ : frame.World → Prop := fun w => w ≠ s
  let ψ : frame.World → Prop := fun w => w = u
  have rel_s_u : frame.rel i1 s u := by aesop
  have rel_u_v : frame.rel i1 u v := by aesop
  have succ_s_eq_u :
      ∀ w, frame.rel i1 s w → w = u := by
    intro w hw
    aesop
  have succ_u_eq_v :
      ∀ x, frame.rel i1 u x → x = v := by
    intro x hx
    have hx' : (u = s ∧ x = u) ∨ (u = u ∧ x = v) := by
      simpa [hrel] using hx
    cases hx' with
    | inl h => exact (hsu h.1).elim
    | inr h => exact h.2
  have hRphi_s : R i1 φ s := by
    intro w hw
    have : w = u := succ_s_eq_u w hw
    simpa [φ, this] using hsu
  have hR_Rphi_s : R i1 (R i1 φ) s := by
    intro w hw x hx
    have hw_u : w = u := by aesop
    have hx_v : x = v := by aesop
    simpa [φ, hx_v] using hvs
  have hInd1 : Ind i1 (R i1 φ) (R i1 (R i1 φ)) s := by
    exact ⟨hR_Rphi_s, fun _ => hR_Rphi_s⟩
  have hRpsi_s : R i1 ψ s := by
    intro w hw
    aesop
  have hInd2 : Ind i1 (R i1 φ) (R i1 ψ) s := by
    exact ⟨hR_Rphi_s, fun _ => hRpsi_s⟩
  have hNotCR : ¬ CRB (fun w => w = u) s := by
    intro hCR
    have hsu : trcl connected s u := trcl_single ⟨i1, rel_s_u⟩
    have huv : trcl connected u v := trcl_single ⟨i1, rel_u_v⟩
    have hsv : trcl connected s v := trcl_trans hsu huv
    have : v = u := hCR v hsv
    exact hvu this
  exact ⟨φ, hRphi_s, hInd1, hInd2, hNotCR⟩

lemma Lewis_fails_2i
  (h1 : three_worlds s u v)
  (h2 : two_agents i1 i2)
  (h3 : frame.rel = fun i w1 w2 =>
    (i = i1 ∧ w1 = s ∧ w2 = u) ∨
    (i = i1 ∧ w1 = u ∧ w2 = u) ∨
    (w1 = v ∧ w2 = v) ∨
    (i = i2 ∧ w1 = s ∧ w2 = s) ∨
    (i = i2 ∧ w1 = u ∧ w2 = v))
  : ¬ ∀ (i : Agent) (φ ψ : frame.World → Prop),
      Rg φ s → Ind i (Rg φ) (Rg (Rg φ)) s → Ind i (Rg φ) (Rg ψ) s → CRB ψ s := by
  rw [two_agents] at h2
  rw [three_worlds] at h1
  let φ : frame.World → Prop := fun _ => True
  let ψ : frame.World → Prop := fun w => w ≠ v
  push_neg
  use i1, φ, ψ
  have h41 : Rg φ s := by
    intro i w
    aesop
  have h42a : Rg (Rg φ) s := by
    intro i x
    intro _ w hw
    aesop
  have h42 : Ind i1 (Rg φ) (Rg (Rg φ)) s := by
    constructor
    { exact h42a i1 }
    { intro _; exact h42a }
  have h43 : Ind i1 (Rg φ) (Rg ψ) s := by
    constructor
    { exact h42a i1 }
    { intro hphi i w
      aesop }
  have h44 : ¬ CRB ψ s := by
    rw [CRB]
    push_neg
    use v
    constructor
    · have h5a : connected s u := by use i1; aesop
      have h5b : connected u v := by use i2; aesop
      exact trcl.head h5a (trcl_single h5b)
    · aesop
  aesop

end LewisTheoremOption1

section LewisTheoremOption2

lemma lewis_s_2
  (C1 : ∀ w, Rg φ w)
  (C3 : ∀ w, Ind i (Rg φ) (Rg ψ) w) :
    CRB ψ s := by
  have hRgψ_all : ∀ w, Rg ψ w := fun w => (C3 w).2 (C1 w)
  intro v hv
  induction hv with
  | base h_edge =>
      rename_i x y
      rcases h_edge with ⟨j, hj⟩
      exact (hRgψ_all x) j y hj
  | step _ _ ih =>
      exact ih

end LewisTheoremOption2

end Sillari
