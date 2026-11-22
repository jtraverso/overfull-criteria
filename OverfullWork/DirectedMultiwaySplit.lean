module

public import OverfullWork.DirectedBiasedSplit
public import OverfullWork.SuperregularMergeReserve

@[expose] public section


/-! Carve several equal-density directed subgraphs from an actual host.
Every semidegree and every ordered rectangle is controlled simultaneously. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]
set_option maxHeartbeats 4000000

abbrev ArcStatistic (V : Type u) := V ⊕ (V ⊕ (Finset V × Finset V))

noncomputable def ArcStatistic.value (D : Digraph V) : ArcStatistic V → ℝ
  | .inl v => inDegree D v
  | .inr (.inl v) => outDegree D v
  | .inr (.inr (S,T)) => incidences D S T

noncomputable def ArcStatistic.scale : ArcStatistic V → ℝ
  | .inl _ => Fintype.card V
  | .inr (.inl _) => Fintype.card V
  | .inr (.inr _) => (Fintype.card V:ℝ)^2

def TracksArcStatistics (H D : Digraph V) (p η : ℝ) : Prop :=
  ∀ a : ArcStatistic V, |a.value H-p*a.value D| ≤ η*a.scale

theorem ArcStatistic.scale_nonneg (a : ArcStatistic V) : 0 ≤ a.scale := by
  rcases a with v | v | ⟨S,T⟩ <;> simp [ArcStatistic.scale]

theorem ArcStatistic.value_sdiff (D H : Digraph V) (h : H ≤ D) (a : ArcStatistic V) :
    a.value (D \ H) = a.value D-a.value H := by
  apply eq_sub_of_add_eq
  rcases a with v | v | ⟨S,T⟩ <;> simp only [ArcStatistic.value]
  · exact_mod_cast (residual_semidegrees D H h v).1
  · exact_mod_cast (residual_semidegrees D H h v).2
  · exact_mod_cast DirectedArcSelection.incidence_partition D H h S T

theorem TracksArcStatistics.complement {D H : Digraph V} {p η : ℝ}
    (h : TracksArcStatistics H D p η) (hLe : H ≤ D) :
    TracksArcStatistics (D \ H) D (1-p) η := by
  intro a
  rw [ArcStatistic.value_sdiff D H hLe,show a.value D-a.value H-(1-p)*a.value D =
    -(a.value H-p*a.value D) by ring,abs_neg]
  exact h a

theorem TracksArcStatistics.comp {D H J : Digraph V} {p q η δ : ℝ}
    (hH : TracksArcStatistics H D q η) (hJ : TracksArcStatistics J H p δ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 ≤ η) :
    TracksArcStatistics J D (p*q) (η+δ) := by
  intro a
  rw [show a.value J-(p*q)*a.value D =
    (a.value J-p*a.value H)+p*(a.value H-q*a.value D) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hp]
  have h₁ := hJ a
  have h₂ := (mul_le_mul_of_nonneg_left (hH a) hp).trans
    (mul_le_of_le_one_left (mul_nonneg hη a.scale_nonneg) hp1)
  linarith only [h₁,h₂]

/-- Partition an arbitrary digraph into k equal fractions and the
remaining fraction. The bounds are absolute in the order of the host. -/
theorem exists_equal_fraction_arc_partition_uniform (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (k : ℕ) (γ : ℝ), 0 < γ → (k:ℝ)*γ ≤ 1 → ∀ {W : Type u} [Fintype W] [DecidableEq W] (D : Digraph W), N ≤ Fintype.card W →
      ∃ F : Fin k → Digraph W, ∃ R : Digraph W,
        (∀ i, TracksArcStatistics (F i) D γ ((k:ℝ)*η)) ∧
        TracksArcStatistics R D (1-(k:ℝ)*γ) ((k:ℝ)*η) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, Disjoint (F i) R) ∧
        ∀ x y, D.Adj x y ↔ R.Adj x y ∨ ∃ i, (F i).Adj x y := by
  obtain ⟨N,hN⟩ := DirectedBiasedSplit.exists_selection_uniform.{u} η hη
  refine ⟨N,?_⟩
  intro k γ hγ hSum W _ _ D hn
  let p := fun i : Fin k => γ/(1-(i.val:ℝ)*γ)
  have hProb (i : Fin k) : 0 ≤ p i ∧ p i ≤ 1 ∧ p i*(1-(i.val:ℝ)*γ) = γ := by
    have hi : (i.val:ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    have hh := (mul_le_mul_of_nonneg_right hi hγ.le).trans hSum
    have hs : γ ≤ 1-(i.val:ℝ)*γ := by nlinarith only [hh]
    have hp : 0 < 1-(i.val:ℝ)*γ := hγ.trans_le hs
    exact ⟨div_nonneg hγ.le hp.le,(div_le_one hp).mpr hs,div_mul_cancel₀ _ hp.ne'⟩
  have hInd (t : ℕ) (ht : t ≤ k) :
      ∃ F : Fin t → Digraph W, ∃ R : Digraph W,
        (∀ i, TracksArcStatistics (F i) D γ ((t:ℝ)*η)) ∧
        TracksArcStatistics R D (1-(t:ℝ)*γ) ((t:ℝ)*η) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, Disjoint (F i) R) ∧
        ∀ x y, D.Adj x y ↔ R.Adj x y ∨ ∃ i, (F i).Adj x y := by
    induction t with
    | zero => exact ⟨Fin.elim0,D,fun i => i.elim0,by intro a; simp,fun i => i.elim0,
        fun i => i.elim0,by simp⟩
    | succ t ih =>
      obtain ⟨F,R,hF,hR,hDis,hFR,hParts⟩ := ih (Nat.le_of_succ_le ht)
      let j : Fin k := ⟨t,by omega⟩
      obtain ⟨H,hHR,hIn,hOut,hCut⟩ := hN (p j) (hProb j).1 (hProb j).2.1 R hn
      have hLocal : TracksArcStatistics H R (p j) η := by
        rintro (v | v | ⟨S,T⟩)
        · exact (hIn v).le
        · exact (hOut v).le
        · exact (hCut S T).le
      have hStep := TracksArcStatistics.comp hR hLocal (hProb j).1 (hProb j).2.1
        (mul_nonneg (Nat.cast_nonneg t) hη.le)
      have hNew := TracksArcStatistics.comp hR (hLocal.complement hHR)
        (sub_nonneg.mpr (hProb j).2.1) (sub_le_self _ (hProb j).1)
        (mul_nonneg (Nat.cast_nonneg t) hη.le)
      have hProd : (1-p j)*(1-(t:ℝ)*γ) = 1-((t+1:ℕ):ℝ)*γ := by
        have hh : p j*(1-(t:ℝ)*γ) = γ := (hProb j).2.2
        push_cast
        linarith only [hh]
      have hErr : (t:ℝ)*η+η = ((t+1:ℕ):ℝ)*η := by push_cast; ring
      have hOld (i : Fin t) : TracksArcStatistics (F i) D γ (((t+1:ℕ):ℝ)*η) := by
        intro a
        rw [←hErr,add_mul]
        exact (hF i a).trans (le_add_of_nonneg_right (mul_nonneg hη.le a.scale_nonneg))
      have hH : TracksArcStatistics H D γ (((t+1:ℕ):ℝ)*η) := by
        have hh : p j*(1-(t:ℝ)*γ) = γ := (hProb j).2.2
        rwa [hh,hErr] at hStep
      have hRestLe : R \ H ≤ R := fun _ _ h => h.1
      have hSep := DirectedArcSelection.exact_partition R H hHR
      refine ⟨Fin.snoc F H,R \ H,?_,by rwa [hProd,hErr] at hNew,?_,?_,?_⟩
      · intro i
        exact Fin.lastCases (by simpa using hH) (fun a => by simpa using hOld a) i
      · intro i l
        refine Fin.lastCases ?_ (fun a => ?_) i
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) l
          simpa using ((hFR b).mono_right hHR).symm
        · refine Fin.lastCases (fun _ => ?_) (fun b h => ?_) l
          · simpa using (hFR a).mono_right hHR
          · simpa using hDis a b (fun he => h (congrArg Fin.castSucc he))
      · intro i
        exact Fin.lastCases (by simpa using hSep.2) (fun a => by simpa using (hFR a).mono_right hRestLe) i
      · intro x y
        have hPartR : R.Adj x y ↔ H.Adj x y ∨ (R \ H).Adj x y := by
          have h := congrArg (fun G : Digraph W => G.Adj x y) hSep.1
          exact h.symm.to_iff.trans (Digraph.sup_adj _ _ _ _)
        rw [hParts x y,hPartR]
        have he : (∃ i, (@Fin.snoc t (fun _ => Digraph W) F H i).Adj x y) ↔ H.Adj x y ∨ ∃ i,(F i).Adj x y := by
          constructor
          · rintro ⟨i,hi⟩
            exact Fin.lastCases (fun hi => Or.inl (by simpa using hi))
              (fun a hi => Or.inr ⟨a,by simpa using hi⟩) i hi
          · rintro (h|⟨i,hi⟩)
            · exact ⟨Fin.last t,by simpa using h⟩
            · exact ⟨i.castSucc,by simpa using hi⟩
        rw [he]
        tauto
  exact hInd k le_rfl

theorem exists_equal_fraction_arc_partition (k : ℕ) (γ η : ℝ)
    (hγ : 0 < γ) (hSum : (k:ℝ)*γ ≤ 1) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (D : Digraph W), N ≤ Fintype.card W →
      ∃ F : Fin k → Digraph W, ∃ R : Digraph W,
        (∀ i, TracksArcStatistics (F i) D γ ((k:ℝ)*η)) ∧
        TracksArcStatistics R D (1-(k:ℝ)*γ) ((k:ℝ)*η) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, Disjoint (F i) R) ∧
        ∀ x y, D.Adj x y ↔ R.Adj x y ∨ ∃ i, (F i).Adj x y := by
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} η hη
  exact ⟨N,hN k γ hγ hSum⟩

end OverfullWork.DirectedRobustExpansion
