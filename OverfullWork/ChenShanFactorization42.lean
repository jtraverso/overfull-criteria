module

public import OverfullWork.ChenShanTheorem42
public import OverfullWork.ChenShanLemma39
public import OverfullWork.CopyColouringExtraction
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset
open scoped Classical
universe u

private theorem card_filter_eq_sum_of_zero_one {I : Type*} [Fintype I]
    (f : I → ℕ) (hf : ∀ i, f i ≤ 1) :
    (univ.filter (fun i => f i = 1)).card = ∑ i, f i := by
  rw [card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro i _
  have h := hf i
  split_ifs <;> omega

private theorem exists_copy_colours_with_incidence {V : Type*} [Fintype V] [DecidableEq V]
    {M : MultiGraph V} {k : ℕ} (D : M.EdgeColoring k) :
    ∃ d : MultiGraph.GeneralCopies.Copies M → Fin k,
      (∀ v i x y, v ∈ x.1 → v ∈ y.1 → d x = i → d y = i → x = y) ∧
      ∀ v i, (∃ x, v ∈ x.1 ∧ d x = i) ↔ (D.colourGraph i).degree v = 1 := by
  let F : ∀ e : Sym2 V, Fin (M.mult e) ≃ ↥(D.occupiedColours e) := fun e =>
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,D.occupiedColours_card])
  let d : MultiGraph.GeneralCopies.Copies M → Fin k := fun x => (F x.1 x.2).val
  have hd (x : MultiGraph.GeneralCopies.Copies M) : D.col x.1 (d x) = 1 :=
    (mem_filter.mp (F x.1 x.2).property).2
  refine ⟨d,?_,?_⟩
  · rintro v i ⟨e,x⟩ ⟨f,y⟩ hv hw hc hc'
    have he : 0 < D.col e i := by rw [← hc]; exact (hd ⟨e,x⟩).symm ▸ Nat.zero_lt_one
    have hf : 0 < D.col f i := by rw [← hc']; exact (hd ⟨f,y⟩).symm ▸ Nat.zero_lt_one
    have hef := D.eq_of_incident_positive hv hw he hf
    change e = f at hef
    subst f
    have hxy : F e x = F e y := Subtype.ext (hc.trans hc'.symm)
    rw [(F e).injective hxy]
  · intro v i
    constructor
    · rintro ⟨x,hv,hi⟩
      have h := single_le_sum (s := univ.filter (fun e : Sym2 V => v ∈ e))
        (f := fun e => D.col e i) (fun _ _ => Nat.zero_le _)
        (mem_filter.mpr ⟨mem_univ _,hv⟩ : x.1 ∈ univ.filter (fun e : Sym2 V => v ∈ e))
      have hf := hd x
      rw [hi] at hf
      have htop := D.colourGraph_degree_le_one i v
      change D.col x.1 i ≤ (D.colourGraph i).degree v at h
      omega
    · intro h
      have hPos : ∃ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), D.col e i ≠ 0 := by
        by_contra! h0
        have hz : (D.colourGraph i).degree v = 0 := sum_eq_zero h0
        omega
      obtain ⟨e,he,hn⟩ := hPos
      have hOne : D.col e i = 1 := by have := D.bundle_colour_le_one e i; omega
      obtain ⟨x,hx⟩ := (F e).surjective ⟨i,mem_filter.mpr ⟨mem_univ _,hOne⟩⟩
      exact ⟨⟨e,x⟩,(mem_filter.mp he).2,congrArg Subtype.val hx⟩

set_option maxHeartbeats 2200000 in
/-- Chen–Shan, Theorem 4.2. The simple core has one edge for each
pair accepted by E. The other edges are the individually indexed
copies of M, so the combined graph also permits parallel copies. -/
theorem exists_factorization_of_dense_bipartite_core (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ m₀ : ℕ, 0 < ε ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ,
      ∀ (A B Z : Type u) [Fintype A] [Fintype B] [Fintype Z]
        (E : A → B → Prop) (M : MultiGraph (A ⊕ (B ⊕ Z))),
      Fintype.card A = m → Fintype.card B = m → Even (Fintype.card Z) →
      (∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ)) →
      (∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ)) →
      (∀ a, Fintype.card {b // E a b} + M.degree (.inl a) = k) →
      (∀ b, Fintype.card {a // E a b} + M.degree (.inr (.inl b)) = k) →
      (∀ z, M.degree (.inr (.inr z)) = k) →
      (∀ a, (M.degree (.inl a) : ℝ) ≤ ε*m) →
      (∀ b, (M.degree (.inr (.inl b)) : ℝ) ≤ ε*m) →
      Nonempty (M.EdgeColoring k) →
      let H := {ab : A × B // E ab.1 ab.2}
      let X := MultiGraph.GeneralCopies.Copies M
      ∃ c : H ⊕ X → Fin k, ∀ v w, ∃! e : H ⊕ X,
        Sum.elim (fun h => Sum.inl h.val.1 = v ∨ .inr (.inl h.val.2) = v)
          (fun x => v ∈ x.1) e ∧ c e = w := by
  obtain ⟨ε,N,hε,hExtend⟩ := exists_factorization_of_balanced_outside_coloring.{u} η hη
  refine ⟨ε,max N 1,hε,?_⟩
  intro m hm k A B Z _ _ _ E M hA hB hEven hMinA hMinB
    hRegA hRegB hRegZ hMaxA hMaxB ⟨C⟩ H X
  let V := A ⊕ (B ⊕ Z)
  let aEmb : A ↪ V := ⟨Sum.inl,Sum.inl_injective⟩
  let bEmb : B ↪ V := ⟨fun b => .inr (.inl b),Sum.inr_injective.comp Sum.inl_injective⟩
  let zEmb : Z ↪ V := ⟨fun z => .inr (.inr z),Sum.inr_injective.comp Sum.inr_injective⟩
  let S := univ.map aEmb
  let T := univ.map bEmb
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    simp [S,T,aEmb,bEmb]
  have hZ : (S ∪ T)ᶜ = univ.map zEmb := by
    ext v
    rcases v with a | (b | z) <;> simp [S,T,aEmb,bEmb,zEmb] <;> intro x h <;> cases Sum.inr.inj h
  have hSumCore : (∑ a, Fintype.card {b // E a b}) = ∑ b, Fintype.card {a // E a b} := by
    simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter]
    exact sum_comm
  have hSumA := sum_congr (s₁ := (univ : Finset A)) rfl (fun a _ => hRegA a)
  have hSumB := sum_congr (s₁ := (univ : Finset B)) rfl (fun b _ => hRegB b)
  rw [sum_add_distrib,sum_const,card_univ,hA] at hSumA
  rw [sum_add_distrib,sum_const,card_univ,hB] at hSumB
  have hSums : (∑ v ∈ S, M.degree v) = ∑ v ∈ T, M.degree v := by
    rw [show S = univ.map aEmb from rfl,show T = univ.map bEmb from rfl,sum_map,sum_map]
    change (∑ a : A, M.degree (.inl a)) = ∑ b : B, M.degree (.inr (.inl b))
    omega
  have hRegOutside : ∀ v ∈ (S ∪ T)ᶜ, M.degree v = k := by
    rw [hZ]
    intro v hv
    obtain ⟨z,_,rfl⟩ := mem_map.mp hv
    exact hRegZ z
  obtain ⟨D,hBalanced,_,hSaturated,hAverage⟩ :=
    exists_balanced_equitable_outside_coloring C S T hST
      (by simpa only [hZ,card_map,card_univ] using hEven) hRegOutside hSums
  obtain ⟨d₀,hd,hUsed⟩ := exists_copy_colours_with_incidence D
  let W := ULift.{u} (Fin k)
  let d (x : X) : W := ⟨d₀ x⟩
  let p := fun x : X => (MultiGraph.GeneralCopies.ends M x).1
  let q := fun x : X => (MultiGraph.GeneralCopies.ends M x).2
  let used := OutsideCoreUsesColor p q d
  have hIncident (x : X) (v : V) : OutsideCoreIncident p q x v ↔ v ∈ x.1 :=
    MultiGraph.GeneralCopies.incident_iff M x v
  have hUse (v : V) (i : W) : used v i ↔ (D.colourGraph i.down).degree v = 1 := by
    change (∃ x, OutsideCoreIncident p q x v ∧ d x = i) ↔ _
    rw [← hUsed v i.down]
    apply exists_congr
    intro x
    exact and_congr (hIncident x v)
      ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
  have hUseCard (v : V) : (univ.filter (used v)).card = M.degree v := by
    simp_rw [hUse v]
    rw [card_filter_eq_sum_of_zero_one _ (fun i : W => D.colourGraph_degree_le_one i.down v)]
    exact (Fintype.sum_equiv (Equiv.ulift : W ≃ Fin k) _ _ (fun _ => rfl)).trans
      (sum_colour_degrees_at_vertex D v)
  have hUseA (i : W) : ((univ.filter (fun a => used (.inl a) i)).card : ℤ) = sideCount D S i.down := by
    simp_rw [hUse]
    rw [card_filter_eq_sum_of_zero_one _ (fun a => D.colourGraph_degree_le_one i.down (.inl a))]
    simp only [Nat.cast_sum,sideCount,S,sum_map,aEmb,Function.Embedding.coeFn_mk]
  have hUseB (i : W) : ((univ.filter (fun b => used (.inr (.inl b)) i)).card : ℤ) = sideCount D T i.down := by
    simp_rw [hUse]
    rw [card_filter_eq_sum_of_zero_one _ (fun b => D.colourGraph_degree_le_one i.down (.inr (.inl b)))]
    simp only [Nat.cast_sum,sideCount,T,sum_map,bEmb,Function.Embedding.coeFn_mk]
  have hTotal : (∑ v ∈ S, (M.degree v : ℝ)) ≤ ε*m*m := by
    rw [show S = univ.map aEmb from rfl,sum_map]
    calc
      _ ≤ ∑ _a : A, ε*m := sum_le_sum (fun a _ => hMaxA a)
      _ = _ := by simp [hA,mul_comm,mul_left_comm]
  have hmPos : (0:ℝ) < m := by exact_mod_cast (show 0 < m from (le_max_right N 1).trans hm)
  let a := (Fintype.card_pos_iff.mp (by rw [hA]; exact_mod_cast hmPos) : Nonempty A).some
  have hkLower : (m:ℝ)/2 ≤ k := by
    have hk := hRegA a
    have hbaseN : Fintype.card {b // E a b} ≤ k := by omega
    rw [Fintype.card_subtype] at hbaseN
    have hbase : ((univ.filter (E a)).card : ℝ) ≤ k := by exact_mod_cast hbaseN
    calc
      _ ≤ (1/2+η)*m := by nlinarith only [hmPos,hη,mul_nonneg hη.le hmPos.le]
      _ ≤ _ := (hMinA a).trans hbase
  have hkPos : (0:ℝ) < k := (by positivity : 0 < (m:ℝ)/2).trans_le hkLower
  have hClass (i : W) : ((univ.filter (fun a => used (.inl a) i)).card : ℝ) ≤ 2*ε*m+2 := by
    have hAvg := hAverage i.down
    rw [← hUseA i] at hAvg
    have hAvgR : (k:ℝ) * ((univ.filter (fun a => used (.inl a) i)).card : ℝ) ≤
        (∑ v ∈ S, (M.degree v : ℝ)) + 2*k := by exact_mod_cast hAvg
    have hScale := mul_le_mul_of_nonneg_right hkLower (show 0 ≤ ε*m by positivity)
    have h := hAvgR.trans (add_le_add_left hTotal _)
    by_contra! hh
    have hcontra := mul_lt_mul_of_pos_left hh hkPos
    nlinarith only [h,hScale,hcontra]
  obtain ⟨c,_,hc⟩ := hExtend m ((le_max_left N 1).trans hm) A B Z W X E p q d
    hA hB hMinA hMinB
    (fun a => by rw [Fintype.card_subtype (p := used (.inl a)),hUseCard]; simpa only [W,Fintype.card_ulift,Fintype.card_fin] using hRegA a)
    (fun b => by rw [Fintype.card_subtype (p := used (.inr (.inl b))),hUseCard]; simpa only [W,Fintype.card_ulift,Fintype.card_fin] using hRegB b)
    (fun v i x y hx hy h₁ h₂ => hd v i.down x y ((hIncident x v).mp hx) ((hIncident y v).mp hy)
      (congrArg ULift.down h₁) (congrArg ULift.down h₂))
    (fun z i => (hUse _ _).mpr (hSaturated _ (by rw [hZ]; exact mem_map.mpr ⟨z,mem_univ _,rfl⟩) i.down))
    (fun a => by rw [hUseCard]; exact hMaxA a)
    (fun b => by rw [hUseCard]; exact hMaxB b)
    (fun i => by
      rw [Fintype.card_subtype,Fintype.card_subtype]
      exact_mod_cast ((hUseA i).trans ((hBalanced i.down).trans (hUseB i).symm)))
    hClass
  refine ⟨fun e => (c e).down,fun v i => ?_⟩
  refine (existsUnique_congr (fun e => ?_)).mp (hc v (ULift.up i))
  have hColor : c e = ULift.up i ↔ (c e).down = i :=
    ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
  cases e with
  | inl e => exact and_congr Iff.rfl hColor
  | inr x => exact and_congr (hIncident x v) hColor

end OverfullWork.ChenShan
