module

public import OverfullWork.KuhnOsthusExtenderStyles
public import OverfullWork.KuhnOsthusChordScheduling
public import OverfullWork.KuhnOsthusExceptionalContraction

@[expose] public section


/-! Choose the untouched and chord styles and bound both endpoint
contributions to equation (8.2) of Kühn–Osthus. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V I : Type*} [Fintype V]

theorem card_cluster_styles (cluster : V → I) (label : V → Fin 50) (u : ℕ)
    (hCell : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u)
    (i : I) (S : Finset (Fin 50)) :
    (univ.filter (fun x => cluster x = i ∧ label x ∈ S)).card = S.card*u := by
  let cell (j : Fin 50) := univ.filter (fun x => cluster x = i ∧ label x = j)
  have he : univ.filter (fun x => cluster x = i ∧ label x ∈ S) = S.biUnion cell := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,cell]
    exact ⟨fun ⟨hi,hs⟩ => ⟨label x,hs,hi,rfl⟩,fun ⟨j,hj,hi,hs⟩ => ⟨hi,hs.symm ▸ hj⟩⟩
  rw [he,card_biUnion]
  · simp [cell,hCell]
  · intro j _ k _ hjk
    exact disjoint_left.mpr (fun x hx hy =>
      hjk (((mem_filter.mp hx).2.2).symm.trans (mem_filter.mp hy).2.2))

/-- The choice of styles supplies the physical sizes, freshness and
disjointness used by the chord matching and the final successor pairs. -/
theorem exists_extender_vertex_pools
    (Q : Digraph V) (cluster : V → I) (label : V → Fin 50) (u : ℕ)
    (S : Finset (Fin 50)) (hS : S.card ≤ 5) (hStyle : SupportedByStyles label ∅ S Q)
    (hCell : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u) :
    ∃ E F : Finset (Fin 50), E.card = 24 ∧ F.card = 21 ∧
      let A i := univ.filter (fun x => cluster x = i ∧ label x ∈ E)
      let B i := univ.filter (fun x => cluster x = i ∧ label x ∈ F)
      (∀ i, (A i).card = 24*u ∧ (B i).card = 21*u) ∧
      (∀ i, A i ⊆ univ.filter (fun x => cluster x = i) ∧
        B i ⊆ univ.filter (fun x => cluster x = i)) ∧
      (∀ i, Disjoint (A i) (B i)) ∧
      ∀ i v, v ∈ A i ∨ v ∈ B i → ¬ IncidentTo Q v := by
  obtain ⟨E,F,hE,hF,hSE,hSF,hEF⟩ := exists_extender_style_allocation S hS
  refine ⟨E,F,hE,hF,fun i => ⟨(card_cluster_styles cluster label u hCell i E).trans (by rw [hE]),
    (card_cluster_styles cluster label u hCell i F).trans (by rw [hF])⟩,?_,?_,?_⟩
  · intro i
    exact ⟨fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩,
      fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩⟩
  · intro i
    exact disjoint_left.mpr (fun x ha hb =>
      disjoint_left.mp hEF (mem_filter.mp ha).2.2 (mem_filter.mp hb).2.2)
  · intro i v hv h
    have hs := hStyle v (notMem_empty v) h
    rcases hv with ha | hb
    · exact disjoint_left.mp hSE hs (mem_filter.mp ha).2.2
    · exact disjoint_left.mp hSF hs (mem_filter.mp hb).2.2

/-- In any cluster, at most one arc of the basic path system can use
a given ordinary endpoint in each role. Five styles cost at most
(m/10) endpoint requests in each direction. -/
theorem extender_endpoint_load_of_styles
    (Q : Digraph V) (cluster : V → I) (label : V → Fin 50)
    (s : Equiv.Perm I) (S : Finset (Fin 50)) (u : ℕ) (hS : S.card ≤ 5)
    (hCell : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u)
    (hQ : IsDirectedPathSystem Q) (hStyle : SupportedByStyles label ∅ S Q) :
    ∀ i,
      10*(∑ j : Arc Q, if s.symm (cluster j.val.2) = i then (1 : ℕ) else 0) ≤ 50*u ∧
      10*(∑ j : Arc Q, if s (cluster j.val.1) = i then (1 : ℕ) else 0) ≤ 50*u := by
  intro i
  have hCard (j : I) :
      10*(univ.filter (fun x => cluster x = j ∧ label x ∈ S)).card ≤ 50*u := by
    rw [card_cluster_styles cluster label u hCell j S,←Nat.mul_assoc]
    exact Nat.mul_le_mul_right u (by omega)
  constructor
  · rw [←card_filter]
    refine le_trans (Nat.mul_le_mul_left _ ?_) (hCard (s i))
    apply card_le_card_of_injOn (fun a : Arc Q => a.val.2)
    · intro a ha
      have he := congrArg s (mem_filter.mp (mem_coe.mp ha)).2
      exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _,by simpa only [Equiv.apply_symm_apply] using he,
        hStyle _ (notMem_empty _) (Or.inr ⟨_,a.prop⟩)⟩)
    · intro a _ b _ he
      change a.val.2 = b.val.2 at he
      exact Subtype.ext (Prod.ext (hQ.in_unique a.prop (he.symm ▸ b.prop)) he)
  · rw [←card_filter]
    refine le_trans (Nat.mul_le_mul_left _ ?_) (hCard (s.symm i))
    apply card_le_card_of_injOn (fun a : Arc Q => a.val.1)
    · intro a ha
      have he := congrArg s.symm (mem_filter.mp (mem_coe.mp ha)).2
      exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _,by simpa only [Equiv.symm_apply_apply] using he,
        hStyle _ (notMem_empty _) (Or.inl ⟨_,a.prop⟩)⟩)
    · intro a _ b _ he
      change a.val.1 = b.val.1 at he
      exact Subtype.ext (Prod.ext he (hQ.out_unique a.prop (he.symm ▸ b.prop)))

/-- The routing step of Lemma 8.3. The total size of the system
controls the number of saturated clusters, and the five styles
control both endpoint contributions. -/
theorem exists_extender_chord_schedule [Fintype I]
    (G : Digraph I) (Q : Digraph V) (cluster : V → I) (label : V → Fin 50)
    (s : Equiv.Perm I) (S : Finset (Fin 50)) (u r g t cap budget : ℕ)
    (hQ : IsDirectedPathSystem Q) (hStyle : SupportedByStyles label ∅ S Q) (hS : S.card ≤ 5)
    (hCell : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u)
    (hRobust : IsRobustAt G r t) (hg : 0 < g) (hAvoid : 2*budget+g ≤ r)
    (hOut : ∀ i, t+2*budget ≤ outDegree G i) (hIn : ∀ i, t ≤ inDegree G i)
    (hMass : Fintype.card (Arc Q) * (2*(Fintype.card I/g+3)) < cap*(budget+1))
    (hCap : 100*(cap+2) ≤ 50*u) :
    ∃ l : Arc Q → List I,
      (∀ j : Arc Q, DirectedListRoutes.Route (reindexSources G s.symm)
        (cluster j.val.2) (s (cluster j.val.1)) (l j)) ∧
      ∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ 50*u ∧
        10*(∑ j : Arc Q, if s.symm (cluster j.val.2) = i then (1 : ℕ) else 0) ≤ 50*u ∧
        10*(∑ j : Arc Q, if s (cluster j.val.1) = i then (1 : ℕ) else 0) ≤ 50*u := by
  obtain ⟨l,hRoutes,hLoad⟩ := exists_chord_routes_with_bounded_interior_load G s
    (fun j : Arc Q => cluster j.val.2) (fun j : Arc Q => s (cluster j.val.1))
    r g t cap budget hRobust hg hAvoid (fun _ => hOut _) (fun _ => hIn _) hMass
  exact ⟨l,fun j => (hRoutes j).1,fun i => ⟨
    (Nat.mul_le_mul_left _ (hLoad i)).trans hCap,
    extender_endpoint_load_of_styles Q cluster label s S u hS hCell hQ hStyle i⟩⟩

/-- Explicit slack in the saturated-cluster count of Lemma 8.3.
Here the route bound and integer saturation threshold have already
been rounded. -/
theorem extender_chord_schedule_mass
    (a n q m s g cap budget : ℕ) (ν : ℝ)
    (hν : 0 < ν) (hq : 0 < q) (hm : 0 < m)
    (hOrder : n ≤ 2*q*m)
    (hSlots : (10^7 : ℝ) ≤ (s : ℝ)*ν^2)
    (hArcs : (a : ℝ) ≤ 1230*(n : ℝ)/(s : ℝ))
    (hRoute : ((q/g+3 : ℕ) : ℝ) ≤ 3/ν)
    (hCap : m ≤ 120*cap)
    (hBudget : ν*(q : ℝ)/4 ≤ (budget : ℝ)+1) :
    a*(2*(q/g+3)) < cap*(budget+1) := by
  have hn : (n : ℝ) ≤ 2*(q : ℝ)*(m : ℝ) := by exact_mod_cast hOrder
  have hs : (0 : ℝ) < s := by
    by_contra! hs'
    exact (not_le_of_gt (by norm_num : (0 : ℝ) < 10^7))
      (hSlots.trans (mul_nonpos_of_nonpos_of_nonneg hs' (sq_nonneg _)))
  have hArc' : (a : ℝ) ≤ (2460/10^7)*(q : ℝ)*(m : ℝ)*ν^2 := by
    apply hArcs.trans
    apply (div_le_iff₀ hs).mpr
    have hb := mul_le_mul_of_nonneg_left hSlots
      (show (0 : ℝ) ≤ (2460/10^7)*(q : ℝ)*(m : ℝ) by positivity)
    linarith only [hb,mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 1230)]
  have hroute' : 2*(((q/g+3 : ℕ) : ℝ)) ≤ 6/ν := by
    calc
      _ ≤ 2*(3/ν) := mul_le_mul_of_nonneg_left hRoute (by norm_num)
      _ = _ := by rw [←mul_div_assoc]; norm_num
  have hLoad := mul_le_mul hArc' hroute'
    (show (0 : ℝ) ≤ 2*(((q/g+3 : ℕ) : ℝ)) by positivity)
    (show (0 : ℝ) ≤ (2460/10^7)*(q : ℝ)*(m : ℝ)*ν^2 by positivity)
  have he : (2460/10^7)*(q : ℝ)*(m : ℝ)*ν^2*(6/ν) =
      (14760/10^7)*(q : ℝ)*(m : ℝ)*ν := by
    field_simp
    norm_num
  rw [he] at hLoad
  have hCap' : (m : ℝ)/120 ≤ (cap : ℝ) := by
    have h : (m : ℝ) ≤ 120*(cap : ℝ) := by exact_mod_cast hCap
    linarith only [h]
  have hRoom := mul_le_mul hCap' hBudget (show (0 : ℝ) ≤ ν*(q : ℝ)/4 by positivity)
    (show (0 : ℝ) ≤ (cap : ℝ) by positivity)
  have hPos : (0 : ℝ) < (q : ℝ)*(m : ℝ)*ν :=
    mul_pos (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hm)) hν
  have hFinal : (a : ℝ)*(2*(((q/g+3 : ℕ) : ℝ))) < (cap : ℝ)*((budget : ℝ)+1) := by
    linarith only [hLoad,hRoom,hPos]
  exact_mod_cast hFinal

end OverfullWork.DirectedRobustExpansion
