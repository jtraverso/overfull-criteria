module

public import OverfullWork.KuhnOsthusExtenderRoutePreparation
public import OverfullWork.KuhnOsthusSparsePathExtender
public import OverfullWork.RobustClusterQuotient

@[expose] public section


/-! The local extension in Kühn–Osthus Lemmas 8.3–8.4 from physical
pair bounds. Deletion is charged once per vertex, including for the
union of all untouched styles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
universe u
variable {V I : Type*} [Fintype V]

private theorem inDegree_le_of_arc_inclusion {D H : Digraph V} (h : D ≤ H) (v : V) :
    inDegree D v ≤ inDegree H v :=
  card_le_card (fun _ hv => mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hv).2⟩)

private theorem residual_rectangle_lower (D L : Digraph V) (S T : Finset V)
    (d η η' : ℝ) (m k : ℕ) (hd : 0 ≤ d) (hη : η ≤ η')
    (hCut : η'*(m:ℝ) ≤ (S.card:ℝ))
    (hLoss : ∀ v, inDegree L v ≤ k)
    (hBudget : (k:ℝ) ≤ (η'-η)*d*(η'*m))
    (hRect : (1-η)*d*(S.card:ℝ)*(T.card:ℝ) ≤ incidences D S T) :
    (1-η')*d*(S.card:ℝ)*(T.card:ℝ) ≤ incidences (D \ L) S T := by
  let M := D ⊓ L
  have hEq : D \ M = D \ L := by
    ext x y
    exact ⟨fun ⟨ha,hb⟩ => ⟨ha,fun h => hb ⟨ha,h⟩⟩,fun ⟨ha,hb⟩ => ⟨ha,fun h => hb h.2⟩⟩
  have hPart : (incidences (D \ L) S T:ℝ) + incidences M S T = incidences D S T := by
    rw [←hEq]
    exact_mod_cast DirectedArcSelection.incidence_partition D M inf_le_left S T
  have hBound : (incidences M S T:ℝ) ≤ (T.card:ℝ)*k := by
    exact_mod_cast incidences_le_card_mul_indegree M S T k
      (fun v => (inDegree_le_of_arc_inclusion inf_le_right v).trans (hLoss v))
  have hPay := hBudget.trans
    (mul_le_mul_of_nonneg_left hCut (mul_nonneg (sub_nonneg.mpr hη) hd))
  have hCost := mul_le_mul_of_nonneg_right hPay (Nat.cast_nonneg T.card)
  linarith only [hPart,hBound,hCost,hRect]

private theorem residual_inNeighbours_loss (D L : Digraph V) (S : Finset V) (v : V)
    (k : ℕ) (hLoss : ∀ x, inDegree L x ≤ k) :
    inNeighbours D S v ≤ inNeighbours (D \ L) S v+k := by
  have hSub : D \ (D \ L) ≤ L := by
    intro x y h
    by_contra hn
    exact h.2 ⟨h.1,hn⟩
  exact RobustClusterQuotient.neighbour_loss_of_deleted_indegree D (D \ L)
    (fun _ _ h => h.1) k (fun x => (inDegree_le_of_arc_inclusion hSub x).trans (hLoss x)) S v

private theorem residual_outTo_loss (D L : Digraph V) (S : Finset V) (v : V)
    (k : ℕ) (hLoss : ∀ x, outDegree L x ≤ k) :
    outTo D S v ≤ outTo (D \ L) S v+k := by
  exact residual_inNeighbours_loss (reverseArcs D) (reverseArcs L) S v k hLoss

omit [Fintype V] in
private theorem common_degree_on_mono {D R : Digraph V} (h : D ≤ R)
    (U : Finset V) (x y : V) (incoming : Bool) :
    ((U.filter (fun v => if incoming then D.Adj v x ∧ D.Adj v y else
      D.Adj x v ∧ D.Adj y v)).card:ℝ) ≤
    ((U.filter (fun v => if incoming then R.Adj v x ∧ R.Adj v y else
      R.Adj x v ∧ R.Adj y v)).card:ℝ) := by
  cases incoming <;> apply Nat.cast_le.mpr <;> apply card_le_card
  all_goals
    intro v hv
    have hm := mem_filter.mp hv
    exact mem_filter.mpr ⟨hm.1,h hm.2.1,h hm.2.2⟩

private theorem style_pool_degree {G : Digraph V} (cluster : V → I) (label : V → Fin 50)
    (i : I) (F : Finset (Fin 50)) (v : V) (b : ℝ) (incoming : Bool)
    (hOne : ∀ j : Fin 50, b ≤ ((univ.filter (fun x =>
      (cluster x = i ∧ label x = j) ∧ (if incoming then G.Adj x v else G.Adj v x))).card:ℝ)) :
    (F.card:ℝ)*b ≤ ((univ.filter (fun x =>
      (cluster x = i ∧ label x ∈ F) ∧ (if incoming then G.Adj x v else G.Adj v x))).card:ℝ) := by
  let A (j : Fin 50) := univ.filter (fun x =>
    (cluster x = i ∧ label x = j) ∧ (if incoming then G.Adj x v else G.Adj v x))
  have hEq : univ.filter (fun x => (cluster x = i ∧ label x ∈ F) ∧
      (if incoming then G.Adj x v else G.Adj v x)) = F.biUnion A := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,A]
    exact ⟨fun ⟨⟨hi,hj⟩,ha⟩ => ⟨label x,hj,⟨hi,rfl⟩,ha⟩,
      fun ⟨j,hj,⟨hi,hl⟩,ha⟩ => ⟨⟨hi,hl.symm ▸ hj⟩,ha⟩⟩
  rw [hEq,card_biUnion,Nat.cast_sum,←nsmul_eq_mul,←sum_const]
  · exact sum_le_sum (fun j _ => hOne j)
  · intro j _ l _ hjl
    exact disjoint_left.mpr (fun x hx hy =>
      hjl (((mem_filter.mp hx).2.1.2).symm.trans (mem_filter.mp hy).2.1.2))

/-- Physical pair bounds on the two reserves and their common split
into 50 styles. The per-style degrees are specified for the successor
reserve, including vertices outside that style. -/
structure ExtenderPairBounds {q : ℕ} (G : Digraph (Fin q)) (H R : Digraph V)
    (cluster : V → Fin q) (label : V → Fin 50) (u : ℕ)
    (d p η b c : ℝ) : Prop where
  cells : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u
  cycle_rect : ∀ i (X Y : Finset V), (∀ x ∈ X, cluster x = i) →
    (∀ y ∈ Y, cluster y = finRotate q i) →
    η*(50*u) ≤ (X.card:ℝ) → η*(50*u) ≤ (Y.card:ℝ) →
    (1-η)*d*(X.card:ℝ)*(Y.card:ℝ) ≤ incidences R X Y
  chord_rect : ∀ i j, G.Adj i j → ∀ (X Y : Finset V),
    (∀ x ∈ X, cluster x = i) → (∀ y ∈ Y, cluster y = j) →
    η*(50*u) ≤ (X.card:ℝ) → η*(50*u) ≤ (Y.card:ℝ) →
    (1-η)*p*(X.card:ℝ)*(Y.card:ℝ) ≤ incidences H X Y
  style_in : ∀ i j v, cluster v = finRotate q i →
    b ≤ inNeighbours R (univ.filter (fun x => cluster x = i ∧ label x = j)) v
  style_out : ∀ i j v, cluster v = i →
    b ≤ outTo R (univ.filter (fun x => cluster x = finRotate q i ∧ label x = j)) v
  codeg_in : ∀ i x y, cluster x = finRotate q i → cluster y = finRotate q i →
    x ≠ y → (((univ.filter (fun v => cluster v = i)).filter
      (fun v => R.Adj v x ∧ R.Adj v y)).card:ℝ) ≤ c
  codeg_out : ∀ i x y, cluster x = i → cluster y = i →
    x ≠ y → (((univ.filter (fun v => cluster v = finRotate q i)).filter
      (fun v => R.Adj x v ∧ R.Adj y v)).card:ℝ) ≤ c

/-- Hamilton extension for any small prescribed path system of at most
five styles after a bounded deletion from the reserve. -/
def HasBoundedPathExtension (D : Digraph V) (label : V → Fin 50) (maxArcs k : ℕ) : Prop :=
  ∀ (Q L : Digraph V), IsDirectedPathSystem Q →
    Fintype.card (Arc Q) ≤ maxArcs →
    (∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label ∅ S Q) →
    (∀ v, inDegree L v ≤ k ∧ outDegree L v ≤ k) →
    ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
      (∀ x y, Q.Adj x y → ρ x = y) ∧
      (∀ x, (Q ⊔ (D \ L)).Adj x (ρ x))

set_option maxHeartbeats 1000000 in
/-- Extend a basic path system after any of the prefix deletions in
Lemma 8.4. The same physical bounds and budgets work on every round. -/
theorem exists_hamilton_extension_of_residual_extender
    (d p ε μ ζ ν τ γ η η' : ℝ)
    (hd : 0 < d) (hp : 0 < p) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ) (hζ : 0 < ζ) (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ*d)
    (hScale : 160*ε ≤ (ζ*μ)^2) (hDiscard : 8*ν ≤ τ*(ζ*d)^2)
    (hνDensity : ν < (1-ε)*d*ε) (hη : η ≤ η') (hη' : η' < 1) (hηε : η' ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {q : ℕ}
      (G : Digraph (Fin (q+1))) (H R : Digraph V)
      (cluster : V → Fin (q+1)) (label : V → Fin 50)
      (u e k r g t cap budget maxArcs : ℕ) (b c : ℝ),
      ExtenderPairBounds G H R cluster label u d p η b c →
      (∀ i, ¬ G.Adj i i) →
      IsRobustAt G r t → 0 < g → 2*budget+g ≤ r →
      (∀ i, t+2*budget ≤ outDegree G i) → (∀ i, t ≤ inDegree G i) →
      maxArcs * (2*((q+1)/g+3)) < cap*(budget+1) → 100*(cap+2) ≤ 50*u →
      0 < u → e ≤ u → N ≤ 21*u →
      η'*(50*u) ≤ (e:ℝ)+1 → η'*(50*u) ≤ ε*(21*u) →
      16 ≤ (ζ*d)^2*(21*u) → c ≤ (d/μ)^2*(21*u) →
      (k:ℝ) ≤ (η'-η)*d*(η'*(50*u)) →
      (k:ℝ) ≤ (η'-η)*p*(η'*(50*u)) →
      ζ*d*(50*u)+(k:ℝ) ≤ 21*b →
      HasBoundedPathExtension (H ⊔ R) label maxArcs k := by
  obtain ⟨N,hN⟩ := exists_hamilton_extension_of_sparse_prepared_routes.{u}
    d ε μ ζ ν τ γ hd hε hε1 hμ hζ hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
  refine ⟨N,?_⟩
  intro V _ q G H R cluster label u e k r g t cap budget maxArcs b c hPair hLoop
    hRobust hg hAvoid hOut hIn hMass hCap hu he hSize hChordCut hCycleCut hDiag hCG hPayR hPayH hPayB
    Q L hQ hArcs hStyles hLoss
  obtain ⟨S,hStyleSize,hStyles⟩ := hStyles
  let s := finRotate (q+1)
  obtain ⟨routes,hRoutes,hLoad⟩ := exists_extender_chord_schedule G Q cluster label s S
    u r g t cap budget hQ hStyles hStyleSize (fun i j => by
      convert hPair.cells i j using 2
      ext x
      simp only [mem_filter]) hRobust hg hAvoid hOut hIn
    (by
      rw [Fintype.card_fin]
      exact (Nat.mul_le_mul_right _ hArcs).trans_lt hMass) hCap
  obtain ⟨E,F,hE,hF,hPools,hSub,hDis,hFresh⟩ :=
    exists_extender_vertex_pools Q cluster label u S hStyleSize hStyles (fun i j => by
      convert hPair.cells i j using 2
      ext x
      simp only [mem_filter])
  let A i := @filter V (fun x => cluster x = i ∧ label x ∈ E)
    (fun x => @instDecidableAnd _ _ (Classical.propDecidable (cluster x = i)) _) univ
  let B i := @filter V (fun x => cluster x = i ∧ label x ∈ F)
    (fun x => @instDecidableAnd _ _ (Classical.propDecidable (cluster x = i)) _) univ
  let U i := univ.filter (fun x => cluster x = i)
  let m := 50*u
  have hNat (i : Fin (q+1)) : (U i).card = m := by
    have hc := card_cluster_styles cluster label u (fun i j => by
      convert hPair.cells i j using 2
      ext x
      simp only [mem_filter]) i univ
    rw [card_univ,Fintype.card_fin] at hc
    convert hc using 2
    ext x
    simp only [U,mem_filter,mem_univ,and_true]
  have hCast : (m:ℝ) = 50*u := by simp [m]
  have hCardA (i : Fin (q+1)) : 50*(A i).card = 24*m := by
    rw [(hPools i).1]
    change 50*(24*u) = 24*(50*u)
    ring
  have hCardB (i : Fin (q+1)) : ((B i).card:ℝ) = 21*u := by
    exact_mod_cast (hPools i).2
  have hOldCut {n : ℕ} (h : η'*(m:ℝ) ≤ (n:ℝ)) : η*(50*u) ≤ (n:ℝ) := by
    rw [←hCast]
    exact (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans h
  have hASub (i : Fin (q+1)) : A i ⊆ U i := by
    intro x hx
    have hx' := (hSub i).1 hx
    simpa only [U,mem_filter,mem_univ,true_and] using hx'
  have hBSub (i : Fin (q+1)) : B i ⊆ U i := by
    intro x hx
    have hx' := (hSub i).2 hx
    simpa only [U,mem_filter,mem_univ,true_and] using hx'
  have hChord (i j : Fin (q+1)) (hij : G.Adj i j)
      (X : Finset V) (hX : X ⊆ A i) (Y : Finset V) (hY : Y ⊆ A j)
      (hXL : e < X.card) (hYL : e < Y.card) :
      0 < incidences (H \ L) X Y := by
    have hx : η'*(m:ℝ) ≤ (X.card:ℝ) :=
      (hCast ▸ hChordCut).trans (by exact_mod_cast hXL)
    have hy : η'*(m:ℝ) ≤ (Y.card:ℝ) :=
      (hCast ▸ hChordCut).trans (by exact_mod_cast hYL)
    have hRect := hPair.chord_rect i j hij X Y
      (fun x hx => (mem_filter.mp (hASub i (hX hx))).2)
      (fun y hy => (mem_filter.mp (hASub j (hY hy))).2) (hOldCut hx) (hOldCut hy)
    have hLow := residual_rectangle_lower H L X Y p η η' m k hp.le hη hx
      (fun v => (hLoss v).1) (by rwa [hCast]) hRect
    have hPos : 0 < (1-η')*p*(X.card:ℝ)*(Y.card:ℝ) :=
      mul_pos (mul_pos (mul_pos (sub_pos.mpr hη') hp) (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hXL)))
        (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hYL))
    exact Nat.cast_pos.mp (hPos.trans_le hLow)
  have hRect (i : Fin (q+1)) (X : Finset V) (hX : X ⊆ U i)
      (Y : Finset V) (hY : Y ⊆ U (s i))
      (hx : η'*(m:ℝ) ≤ (X.card:ℝ)) (hy : η'*(m:ℝ) ≤ (Y.card:ℝ)) :
      (1-ε)*d*(X.card:ℝ)*(Y.card:ℝ) ≤ incidences (R \ L) X Y := by
    have hOriginal := hPair.cycle_rect i X Y (fun x hx => (mem_filter.mp (hX hx)).2)
      (fun y hy => (mem_filter.mp (hY hy)).2) (hOldCut hx) (hOldCut hy)
    have hNew := residual_rectangle_lower R L X Y d η η' m k hd.le hη hx
      (fun v => (hLoss v).1) (by rwa [hCast]) hOriginal
    have hFactor : 1-ε ≤ 1-η' := sub_le_sub_left hηε 1
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFactor hd.le) (Nat.cast_nonneg X.card))
      (Nat.cast_nonneg Y.card)).trans hNew
  have hPoolIn (i : Fin (q+1)) (v : V) (hv : v ∈ U (s i)) :
      ζ*d*(m:ℝ) ≤ (inNeighbours (R \ L) (B i) v:ℝ) := by
    have hSum : 21*b ≤ (inNeighbours R (B i) v:ℝ) := by
      have h := style_pool_degree (G := R) cluster label i F v b true
        (fun j => by
          simpa only [inNeighbours,filter_filter,if_true] using
            hPair.style_in i j v (mem_filter.mp hv).2)
      rw [hF,Nat.cast_ofNat] at h
      refine h.trans_eq ?_
      apply congrArg (fun A : Finset V => (A.card : ℝ))
      ext x
      simp only [B,mem_filter,mem_univ,true_and,if_true]
    have h := residual_inNeighbours_loss R L (B i) v k (fun v => (hLoss v).1)
    have hLoss' : (inNeighbours R (B i) v:ℝ) ≤ (inNeighbours (R \ L) (B i) v:ℝ)+k := by
      exact_mod_cast h
    rw [hCast]
    linarith only [hSum,hLoss',hPayB]
  have hPoolOut (i : Fin (q+1)) (v : V) (hv : v ∈ U i) :
      ζ*d*(m:ℝ) ≤ (outTo (R \ L) (B (s i)) v:ℝ) := by
    have hSum : 21*b ≤ (outTo R (B (s i)) v:ℝ) := by
      have h := style_pool_degree (G := R) cluster label (s i) F v b false
        (fun j => by
          simpa only [outTo,filter_filter,Bool.false_eq_true,if_false] using
            hPair.style_out i j v (mem_filter.mp hv).2)
      rw [hF,Nat.cast_ofNat] at h
      refine h.trans_eq ?_
      apply congrArg (fun A : Finset V => (A.card : ℝ))
      ext x
      simp only [B,mem_filter,mem_univ,true_and,Bool.false_eq_true,if_false]
    have h := residual_outTo_loss R L (B (s i)) v k (fun v => (hLoss v).2)
    have hLoss' : (outTo R (B (s i)) v:ℝ) ≤ (outTo (R \ L) (B (s i)) v:ℝ)+k := by
      exact_mod_cast h
    rw [hCast]
    linarith only [hSum,hLoss',hPayB]
  let H' := H \ L
  let R' := R \ L
  obtain ⟨ρ,hC,hKeep,hEdges⟩ := hN G Q H' R' cluster routes A B m e η' c
    hQ hLoop hRoutes (by dsimp [m]; omega) (by dsimp [m]; omega) hCardA hASub
    hBSub hNat hFresh hDis hChord (fun i => (hLoad i).1)
    (fun i => by
      convert (hLoad i).2.1 using 2
      apply sum_congr rfl
      intro j _
      by_cases h : s.symm (cluster j.val.2) = i <;> simp only [s,h,if_true,if_false])
    (fun i => by
      convert (hLoad i).2.2 using 2
      apply sum_congr rfl
      intro j _
      by_cases h : s (cluster j.val.1) = i <;> simp only [s,h,if_true,if_false])
    (fun i => ⟨card_pos.mp (by rw [(hPools i).2]; omega),(hPools i).2 ▸ hSize⟩)
    (fun i => by rwa [hCast,hCardB]) (fun i => by rwa [hCardB]) (fun i => by rwa [hCardB])
    hRect hPoolIn hPoolOut
    (fun i x hx y hy hxy => by
      have h := common_degree_on_mono (D := R') (R := R) (fun _ _ h => h.1) (U i) x y true
      exact h.trans (hPair.codeg_in i x y (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy))
    (fun i x hx y hy hxy => by
      have h := common_degree_on_mono (D := R') (R := R) (fun _ _ h => h.1) (U (s i)) x y false
      exact h.trans (hPair.codeg_out i x y (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy))
  refine ⟨ρ,hC,hKeep,?_⟩
  intro x
  rcases (hEdges x) with (h | ⟨h,hn⟩) | ⟨h,hn⟩
  · exact Or.inl h
  · exact Or.inr ⟨Or.inl h,hn⟩
  · exact Or.inr ⟨Or.inr h,hn⟩

/-- A fixed uniform host style provides a semidegree floor even
after deleting the exceptional factors, before sampling the extender. -/
theorem successor_style_degree_after_host_deletion (D L : Digraph V) (A B : Finset V)
    (v : V) (α θ b : ℝ) (k : ℕ)
    (hθ : θ ≤ α) (hOne : θ ≤ 1)
    (hIn : α*(Fintype.card V:ℝ) ≤ inDegree D v)
    (hOut : α*(Fintype.card V:ℝ) ≤ outDegree D v)
    (hA : UniformProfileCell (fun _ : Unit => univ.filter (fun x => D.Adj x v)) univ A 50 θ)
    (hB : UniformProfileCell (fun _ : Unit => univ.filter (D.Adj v)) univ B 50 θ)
    (hLossI : ∀ x, inDegree L x ≤ k) (hLossO : ∀ x, outDegree L x ≤ k)
    (hMargin : b+(k:ℝ) ≤ (1-θ)*(α*(Fintype.card V:ℝ)/50)) :
    b ≤ inNeighbours (D \ L) A v ∧ b ≤ outTo (D \ L) B v := by
  have hCount (X : Finset V) (P : V → Prop) :
      profileCount X (univ.filter P) = ((X.filter P).card:ℝ) := by
    unfold profileCount
    apply congrArg (fun T : Finset V => (T.card:ℝ))
    ext x
    simp
  have hDistribute (P : V → Prop) (X : Finset V)
      (hFull : α*(Fintype.card V:ℝ) ≤ ((univ.filter P).card:ℝ))
      (hUni : UniformProfileCell (fun _ : Unit => univ.filter P) univ X 50 θ) :
      (1-θ)*(α*(Fintype.card V:ℝ)/50) ≤ ((X.filter P).card:ℝ) := by
    have hTh : θ*((univ : Finset V).card:ℝ) ≤ profileCount univ (univ.filter P) := by
      rw [card_univ,hCount]
      exact (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)).trans hFull
    have hT := (abs_le.mp (hUni () hTh)).1
    simp only [hCount,Nat.cast_ofNat] at hT
    have hL := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hFull (by norm_num : (0:ℝ) ≤ 50)) (sub_nonneg.mpr hOne)
    linarith only [hT,hL]
  have hBlockI := hDistribute (fun x => D.Adj x v) A hIn hA
  have hBlockO := hDistribute (D.Adj v) B hOut hB
  have hWI : (inNeighbours D A v:ℝ) ≤ (inNeighbours (D \ L) A v:ℝ)+k := by
    exact_mod_cast residual_inNeighbours_loss D L A v k hLossI
  have hWO : (outTo D B v:ℝ) ≤ (outTo (D \ L) B v:ℝ)+k := by
    exact_mod_cast residual_outTo_loss D L B v k hLossO
  change _ ≤ (inNeighbours D A v:ℝ) at hBlockI
  change _ ≤ (outTo D B v:ℝ) at hBlockO
  exact ⟨by linarith only [hBlockI,hWI,hMargin],by linarith only [hBlockO,hWO,hMargin]⟩

end OverfullWork.DirectedRobustExpansion
