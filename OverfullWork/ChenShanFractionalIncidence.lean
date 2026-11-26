module

public import OverfullWork.ChenShanSignedEdgeWeights
public import OverfullWork.ChenShanTripartiteCompletion

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

/-- One real weight per possible edge, on each pair of vertex classes. -/
structure TripartiteEdgeWeights (A : Type uA) (B : Type uB) (W : Type uW) where
  ab : A → B → ℝ
  aw : A → W → ℝ
  bw : B → W → ℝ

namespace TripartiteEdgeWeights

def Supported (r : TripartiteEdgeWeights A B W)
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) : Prop :=
  (∀ a b, ¬ E a b → r.ab a b = 0) ∧
  (∀ a w, ¬ L a w → r.aw a w = 0) ∧
  (∀ b w, ¬ R b w → r.bw b w = 0)

def Bounded (r : TripartiteEdgeWeights A B W) (d : ℝ) : Prop :=
  (∀ a b, |r.ab a b| ≤ d) ∧ (∀ a w, |r.aw a w| ≤ d) ∧ (∀ b w, |r.bw b w| ≤ d)

def Balanced [Fintype A] [Fintype B] [Fintype W] (r : TripartiteEdgeWeights A B W) : Prop :=
  (∀ a, (∑ b, r.ab a b) = ∑ w, r.aw a w) ∧
  (∀ b, (∑ a, r.ab a b) = ∑ w, r.bw b w) ∧
  (∀ w, (∑ a, r.aw a w) = ∑ b, r.bw b w)

def sub (r s : TripartiteEdgeWeights A B W) : TripartiteEdgeWeights A B W :=
  ⟨fun a b => r.ab a b - s.ab a b, fun a w => r.aw a w - s.aw a w, fun b w => r.bw b w - s.bw b w⟩

end TripartiteEdgeWeights

def TriangleSupported (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (p : A → B → W → ℝ) : Prop :=
  ∀ a b w, ¬ (E a b ∧ L a w ∧ R b w) → p a b w = 0

def triangleBoundary [Fintype A] [Fintype B] [Fintype W]
    (p : A → B → W → ℝ) : TripartiteEdgeWeights A B W :=
  ⟨fun a b => ∑ w, p a b w, fun a w => ∑ b, p a b w, fun b w => ∑ a, p a b w⟩

/-- The counting hypotheses (4.9) and the balance of the graph. -/
structure DenseTripartite [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (m : ℕ) (η ε : ℝ) : Prop where
  sizeA : Fintype.card A = m
  sizeB : Fintype.card B = m
  balanced : TripartiteLocallyBalanced E L R
  degreeA : ∀ a, (1/2 + η) * m ≤ (#(univ.filter (E a)) : ℝ)
  degreeB : ∀ b, (1/2 + η) * m ≤ (#(univ.filter (fun a => E a b)) : ℝ)
  missingAW : ∀ a, (#(univ.filter (fun w => ¬ L a w)) : ℝ) ≤ ε * m
  missingBW : ∀ b, (#(univ.filter (fun w => ¬ R b w)) : ℝ) ≤ ε * m
  missingWA : ∀ w, (#(univ.filter (fun a => ¬ L a w)) : ℝ) ≤ ε * m
  missingWB : ∀ w, (#(univ.filter (fun b => ¬ R b w)) : ℝ) ≤ ε * m

theorem card_filter_le_inter_add_missing {V : Type*} [Fintype V] (P Q : V → Prop) :
    #(univ.filter P) ≤ #(univ.filter (fun v => P v ∧ Q v)) + #(univ.filter (fun v => ¬ Q v)) := by
  have h := card_filter_add_card_filter_not (s := univ.filter P) Q
  have hm : #((univ.filter P).filter (fun v => ¬ Q v)) ≤ #(univ.filter (fun v => ¬ Q v)) :=
    card_le_card (fun _ hv => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩)
  have hEq : (univ.filter P).filter Q = univ.filter (fun v => P v ∧ Q v) := by
    ext; simp
  rw [hEq] at h
  omega

private theorem card_filtered_subtype {V : Type*} [Fintype V] (P Q : V → Prop) :
    #((univ : Finset {v // Q v}).filter (fun v => P v.val)) =
      #(univ.filter (fun v => P v ∧ Q v)) := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact
    { toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem sum_extend_subtype {V : Type*} [Fintype V]
    (Q : V → Prop) (f : {v // Q v} → ℝ) :
    (∑ v, if h : Q v then f ⟨v,h⟩ else 0) = ∑ v, f v := by
  let g (v : V) := if h : Q v then f ⟨v,h⟩ else 0
  change (∑ v, g v) = _
  have h := sum_subtype (p := Q) (F := inferInstance) (univ.filter Q) (fun v => by simp) g
  rw [sum_filter] at h
  have hg (v : V) : (if Q v then g v else 0) = g v := by
    by_cases hv : Q v <;> simp [g,hv]
  simpa only [hg,g,dite_eq_left,Subtype.property] using h

private theorem sum_supported_subtype {V : Type*} [Fintype V]
    (Q : V → Prop) (f : V → ℝ) (h : ∀ v, ¬ Q v → f v = 0) :
    (∑ v : {v // Q v}, f v.val) = ∑ v : V, f v := by
  rw [← sum_subtype (p := Q) (univ.filter Q) (fun v => by simp) f,sum_filter]
  apply sum_congr rfl
  intro v _
  by_cases hv : Q v <;> simp [hv,h v]

/-- The degree estimate (4.11), stated on a neighbor subtype. -/
theorem subtype_degree_margin {V : Type*} [Fintype V]
    (P Q : V → Prop) (m : ℕ) (η ε : ℝ)
    (hSize : Fintype.card V = m) (hε : ε ≤ η)
    (hDeg : (1/2+η)*m ≤ (#(univ.filter P) : ℝ))
    (hMissing : (#(univ.filter (fun v => ¬ Q v)) : ℝ) ≤ ε*m) :
    (Fintype.card {v // Q v} : ℝ)/2 + η*m/2 ≤
      (#((univ : Finset {v // Q v}).filter (fun v => P v.val)) : ℝ) := by
  rw [card_filtered_subtype, Fintype.card_subtype]
  have hTotal := card_filter_add_card_filter_not (s := (univ : Finset V)) Q
  rw [card_univ,hSize] at hTotal
  have hTotal' : (#(univ.filter Q) : ℝ) + (#(univ.filter (fun v => ¬ Q v)) : ℝ) = m := by
    exact_mod_cast hTotal
  have hLoss : (#(univ.filter P) : ℝ) ≤ (#(univ.filter (fun v => P v ∧ Q v)) : ℝ) +
      (#(univ.filter (fun v => ¬ Q v)) : ℝ) := by exact_mod_cast card_filter_le_inter_add_missing P Q
  have hεm := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg m)
  linarith

/-- The signed correction (4.12) matches both incidence margins by
applying the signed weighting lemma in each neighbor graph. -/
theorem exists_signed_incidence_correction [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    {m : ℕ} {η ε : ℝ} (h : DenseTripartite E L R m η ε)
    (hm : 0 < m) (hη : 0 < η) (hε : ε ≤ η)
    (r : TripartiteEdgeWeights A B W) (d : ℝ) (hd : 0 ≤ d)
    (hr : r.Supported E L R) (hbal : r.Balanced) (hbd : r.Bounded d) :
    ∃ p : A → B → W → ℝ, TriangleSupported E L R p ∧
      (∀ a w, (∑ b, p a b w) = r.aw a w) ∧
      (∀ b w, (∑ a, p a b w) = r.bw b w) ∧
      ∀ a b w, |p a b w| ≤ 2*d/(η*m) := by
  have hg : 0 < η*(m : ℝ)/2 := by positivity
  have hLocal (w : W) :
      ∃ z : {a // L a w} → {b // R b w} → ℝ,
        (∀ a, (∑ b, z a b) = r.aw a.val w) ∧
        (∀ b, (∑ a, z a b) = r.bw b.val w) ∧
        (∀ a b, |z a b| ≤ d/(η*m/2)) ∧
        (∀ a b, ¬ E a.val b.val → z a b = 0) := by
    have hCard := h.balanced.2.2 w
    let n := Fintype.card {a // L a w}
    apply exists_bounded_signed_edge_weights (fun a b => E a.val b.val)
      (fun a => r.aw a.val w) (fun b => r.bw b.val w) n (η*m/2) d hg hd rfl hCard.symm
    · intro a
      dsimp only [n]
      rw [hCard]
      exact subtype_degree_margin (E a.val) (fun b => R b w) m η ε h.sizeB hε (h.degreeA a.val)
        (h.missingWB w)
    · intro b
      exact subtype_degree_margin (fun a => E a b.val) (fun a => L a w) m η ε h.sizeA hε
        (h.degreeB b.val) (h.missingWA w)
    · rw [sum_supported_subtype (fun a => L a w) (fun a => r.aw a w) (fun a => hr.2.1 a w),
        sum_supported_subtype (fun b => R b w) (fun b => r.bw b w) (fun b => hr.2.2 b w)]
      exact hbal.2.2 w
    · exact fun a => hbd.2.1 a.val w
    · exact fun b => hbd.2.2 b.val w
  choose z hRow hCol hBound hZero using hLocal
  let p (a : A) (b : B) (w : W) :=
    if ha : L a w then if hb : R b w then z w ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0
  refine ⟨p,?_,?_,?_,?_⟩
  · intro a b w hSupport
    by_cases ha : L a w
    · by_cases hb : R b w
      · have he : ¬ E a b := fun he => hSupport ⟨he,ha,hb⟩
        simpa only [p,dite_eq_left ha,dite_eq_left hb] using hZero w ⟨a,ha⟩ ⟨b,hb⟩ he
      · simp [p,ha,hb]
    · simp [p,ha]
  · intro a w
    by_cases ha : L a w
    · simp only [p,dite_eq_left ha]
      rw [sum_extend_subtype]
      exact hRow w ⟨a,ha⟩
    · simp [p,ha,hr.2.1 a w ha]
  · intro b w
    by_cases hb : R b w
    · simp only [p,dite_eq_left hb]
      rw [sum_extend_subtype (fun a => L a w) (fun a => z w a ⟨b,hb⟩)]
      exact hCol w ⟨b,hb⟩
    · have hp (a : A) : p a b w = 0 := by by_cases ha : L a w <;> simp [p,ha,hb]
      simp [hp,hr.2.2 b w hb]
  · intro a b w
    have hd' : 0 ≤ 2*d/(η*m) := by positivity
    by_cases ha : L a w
    · by_cases hb : R b w
      · have hEq : d/(η*m/2) = 2*d/(η*m) := by ring
        simpa only [p,dite_eq_left ha,dite_eq_left hb,← hEq] using hBound w ⟨a,ha⟩ ⟨b,hb⟩
      · simpa [p,ha,hb] using hd'
    · simpa [p,ha] using hd'

end OverfullWork.ChenShan
