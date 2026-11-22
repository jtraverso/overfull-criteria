module

public import OverfullWork.KuhnOsthusParityReserveClosure

@[expose] public section


/-! The two switch pairs of each of the remaining parity reserves.
The lane labels are preserved from the triple switch to the
auxiliary switch and through the return. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V : Type*}

def PrescribedSwitchMatching.inHost {D G : Digraph V} {S T : Finset V}
    (M : PrescribedSwitchMatching D S T) (h : ∀ l, G.Adj (M.source l) (M.target l)) :
    PrescribedSwitchMatching G S T :=
  ⟨M.source,M.target,h⟩

structure ParityAuxiliarySwitch (D : Digraph V) (S T : Finset V) where
  diagonal : PrescribedSwitchMatching D S T
  crossed : ∀ l, D.Adj (diagonal.source l) (diagonal.target (!l))

structure TwoSwitchParityFactor {D E : Digraph V} {S T U W : Finset V}
    (P : PrescribedSwitchMatching D S T) (Q : PrescribedSwitchMatching D U W) where
  factor : WindingParityFactor D E
  triple_arcs : ∀ l, factor.permutation (P.source l).val = (P.target l).val
  auxiliary_arcs : ∀ l, factor.permutation (Q.source l).val = (Q.target l).val
  triple_bicycle : MarkedBicycle factor.permutation (P.source false).val (P.source true).val
  auxiliary_bicycle : MarkedBicycle factor.permutation (Q.source false).val (Q.source true).val

variable [Fintype V]

/-- Select the shared C₄ in the residual, with its two complementary
matchings in the lane order. -/
theorem IsLowerSuperregularPair.exists_parity_auxiliary_switch {D : Digraph V} {S T : Finset V}
    {m r : ℕ} {ε d : ℝ} (hp : IsLowerSuperregularPair D ε d S T)
    (hS : S.card = 2*m) (hT : T.card = 2*m) (hm : 0 < m) (hε : 0 ≤ ε)
    (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    Nonempty (ParityAuxiliarySwitch D S T) := by
  obtain ⟨f,u,hf,hCross⟩ := IsLowerSuperregularPair.exists_matching_with_repair_switch D S T m r ε d
    hp hS hT hm hε hGap hd hr hCut hRoute
  let s := cycleAbsorberLane.toEmbedding.trans u
  let t := s.trans f.toEmbedding
  exact ⟨⟨⟨s,t,fun l => hf (s l)⟩,fun l => hCross (cycleAbsorberLane l) (cycleAbsorberLane (!l))⟩⟩

/-- Route through two prescribed matchings and then the exceptional
interval. Both pairs of switch sources are separated by the same
two cycles after the return. -/
theorem exists_two_switch_parity_factor {D H : Digraph V} {k s a c t m r : ℕ} {ε d : ℝ}
    (X : Fin k → Finset V) (hk : 0 < k) (hm : 0 < m)
    (hsa : s+4 ≤ a) (hac : a+4 ≤ c) (hct : c ≤ t) (htk : t < k) (hnt : 3 ≤ k+s-t)
    (hCover : ∀ v, ∃ i, v ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (hPair : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate k i)))
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let A := cyclicCluster X hk
    ∀ (P : PrescribedSwitchMatching D (A s) (A (s+1)))
      (Q : PrescribedSwitchMatching D (A a) (A (a+1)))
      (E : IntervalPathCover H (clusterIntervalVertices A c t) (A c) (A t)),
      Nonempty (TwoSwitchParityFactor (E := E.digraph) P Q) := by
  intro A P Q E
  have pair (i : ℕ) : IsLowerSuperregularPair D ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair D ε d (A i) (cyclicCluster X hk (i+1))
    rw [cyclicCluster_successor]
    exact hPair _
  have apart (i j : ℕ) (hi : i ≤ c) (hj : j ≤ c) (hne : i ≠ j) : Disjoint (A i) (A j) :=
    cyclicCluster_distinct hk hDis (by rwa [Nat.mod_eq_of_lt (by omega : i < k),Nat.mod_eq_of_lt (by omega : j < k)])
  let j₀ : Fin m := ⟨0,hm⟩
  obtain ⟨P₀,hP₀⟩ := P.exists_ordered_pair j₀ (pair s) (hSize _) (hSize _) hε hGap hd hr hCut hRoute
  obtain ⟨Q₀,hQ₀⟩ := Q.exists_ordered_pair j₀ (pair a) (hSize _) (hSize _) hε hGap hd hr hCut hRoute
  obtain ⟨U,hU₀,hU₁⟩ := P₀.exists_join_through_long_route Q₀ (by omega) (by omega) (by omega)
    (2*m) r ε d hε hGap hd hr hCut hRoute (fun i _ _ => hSize _)
    (fun i j _ hi _ hj h => apart i j (by omega) (by omega) h) (fun i _ _ => pair i)
  have hCard : (A c).card = 2*m := hSize _
  let f : Fin m × Fin 2 ≃ A c := (cycleAbsorberSwitchSlot m).trans
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hCard)).symm
  obtain ⟨T,hT,_⟩ := exists_ordered_cluster_paths D A (a+1) c (2*m) r hac
    (U.orderAt _ (by omega) le_rfl) f ε d hε hGap hd hr hCut hRoute
    (fun i _ _ => hSize _) (fun i j _ hi _ hj h => apart i j hi hj h) (fun i _ _ => pair i)
  let L := U.concat T (fun j => (hT j).symm)
  have hL₀ (l : Bool) :
      L.vertex s (j₀,cycleAbsorberLane l) = (P.source l).val ∧
      L.vertex (s+1) (j₀,cycleAbsorberLane l) = (P.target l).val :=
    ⟨(U.concat_left T _ (by omega) _).trans ((hU₀ _ (by omega) _).trans (hP₀ l).1),
     (U.concat_left T _ (by omega) _).trans ((hU₀ _ (by omega) _).trans (hP₀ l).2)⟩
  have hL₁ (l : Bool) :
      L.vertex a (j₀,cycleAbsorberLane l) = (Q.source l).val ∧
      L.vertex (a+1) (j₀,cycleAbsorberLane l) = (Q.target l).val :=
    ⟨(U.concat_left T _ (by omega) _).trans ((hU₁ _ le_rfl _).trans (hQ₀ l).1),
     (U.concat_left T _ (by omega) _).trans ((hU₁ _ (by omega) _).trans (hQ₀ l).2)⟩
  obtain ⟨F,⟨O⟩,hTrace⟩ := L.exists_closed_winding_parity_factor X hk (by omega) (by omega)
    hct htk hnt hCover hDis hSize E hPair hε hGap hd hr hCut hRoute
  have hB := O.bicycle_at_copy j₀
  change MarkedBicycle F.permutation (L.vertex s (j₀,cycleAbsorberLane false))
    (L.vertex s (j₀,cycleAbsorberLane true)) at hB
  rw [(hL₀ false).1,(hL₀ true).1] at hB
  have visit (l : Bool) : F.permutation.SameCycle (P.source l).val (Q.source l).val := by
    have h := hTrace (j₀,cycleAbsorberLane l) (a-s) (by omega)
    change (F.permutation : V → V)^[a-s] (L.vertex s (j₀,cycleAbsorberLane l)) =
      L.vertex (s+(a-s)) (j₀,cycleAbsorberLane l) at h
    rw [(hL₀ l).1,show s+(a-s) = a by omega,(hL₁ l).1] at h
    exact h ▸ successor_sameCycle_iterate F.permutation (P.source l).val (a-s)
  have hB' : MarkedBicycle F.permutation (Q.source false).val (Q.source true).val :=
    ⟨fun h => hB.1 ((visit false).trans (h.trans (visit true).symm)),fun v =>
      (hB.2 v).imp ((visit false).symm.trans) ((visit true).symm.trans)⟩
  have hAt (i : ℕ) (hi : s ≤ i) (hic : i < c) (j : Fin m × Fin 2) :
      F.permutation (L.vertex i j) = L.vertex (i+1) j := by
    have h := hTrace j (i-s) (by omega)
    have h' := hTrace j (i-s+1) (by omega)
    rw [iterate_succ_apply',h] at h'
    rwa [show s+(i-s+1) = i+1 by omega,show s+(i-s) = i by omega] at h'
  refine ⟨⟨F,?_,?_,hB,hB'⟩⟩
  · intro l
    simpa only [(hL₀ l).1,(hL₀ l).2] using hAt s le_rfl (by omega) (j₀,cycleAbsorberLane l)
  · intro l
    simpa only [(hL₁ l).1,(hL₁ l).2] using hAt a (by omega) (by omega) (j₀,cycleAbsorberLane l)

end OverfullWork.DirectedRobustExpansion
