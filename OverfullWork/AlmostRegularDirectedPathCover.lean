module

public import OverfullWork.AdjacentLayerPathCover
public import OverfullWork.UniformProfilePartitions
public import OverfullWork.DirectedRobustExpansion
public import Mathlib.Data.Fintype.Fin

@[expose] public section


/-! The dense-part covering step of GGKLO Lemma 7.3(i).
The layers and the paths are constructed from an almost regular host. -/
namespace OverfullWork.AdjacentLayerPathCover

open Finset DirectedRobustExpansion UniformSubsetSampling RankedDirectedPathCover
open scoped Classical
universe u
set_option maxHeartbeats 6000000

private def balancedSize (k n : ℕ) (i : Fin (k+1)) : ℕ :=
  n/(k+1) + if i.val < n%(k+1) then 1 else 0

private theorem balancedSize_sum (k n : ℕ) : (∑ i, balancedSize k n i) = n := by
  unfold balancedSize
  rw [sum_add_distrib, ← card_filter, Fin.card_filter_val_lt]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    min_eq_right (Nat.mod_lt _ (Nat.succ_pos k)).le]
  calc
    _ = n%(k+1)+(k+1)*(n/(k+1)) := add_comm _ _
    _ = n := Nat.mod_add_div .. 

private theorem balancedSize_bounds (k n : ℕ) (i : Fin (k+1)) :
    (n:ℝ)/((k:ℝ)+1)-1 ≤ (balancedSize k n i:ℝ) ∧
    (balancedSize k n i:ℝ) ≤ (n:ℝ)/((k:ℝ)+1)+1 := by
  have hK : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hq : ((n/(k+1):ℕ):ℝ) ≤ (n:ℝ)/((k:ℝ)+1) := by
    apply (le_div_iff₀ hK).mpr
    exact_mod_cast Nat.div_mul_le_self n (k+1)
  have hq' : (n:ℝ)/((k:ℝ)+1) < ((n/(k+1):ℕ):ℝ)+1 := by
    apply (div_lt_iff₀ hK).mpr
    have h := Nat.lt_mul_div_succ n (Nat.succ_pos k)
    rw [Nat.mul_comm (k+1)] at h
    exact_mod_cast h
  unfold balancedSize
  split_ifs <;> constructor <;> push_cast <;> linarith only [hq,hq']

private theorem layer_card_filter {V : Type*} [Fintype V] {k : ℕ}
    (rank : V → Fin (k+1)) (i : Fin (k+1)) (P : V → Prop) :
    ((univ : Finset (Layer rank i)).filter (fun x => P x.val)).card =
      (slice rank i ∩ univ.filter P).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_inter.mpr ⟨(mem_slice _ _ _).mpr x.prop,
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hi,hx⟩ := mem_inter.mp hx
    exact ⟨⟨x,(mem_slice _ _ _).mp hi⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,rfl⟩

/-- For a fixed number of layers, sufficiently large almost regular
digraphs have a spanning directed path cover with few paths. The proof
uses fixed-size neighbourhood concentration and adjacent-layer matchings. -/
theorem exists_cover_uniform_in_density (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → 4*η ≤ δ → ∀ {V : Type u} [Fintype V] (D : Digraph V), N ≤ Fintype.card V →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
        (inDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ) ∧
        (outDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
        ((terminals H.Adj (univ : Finset V)).card:ℝ) ≤
          (1+η+(k:ℝ)*(η+12*η/δ))*((Fintype.card V:ℝ)/((k:ℝ)+1)) := by
  let K : ℝ := (k:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hTol : 0 < η/K := div_pos hη hK
  obtain ⟨N₀,hSample⟩ := exists_partition_profile_threshold.{u,0,u} 2 (η/K) (by norm_num) hTol
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (K/η)
  refine ⟨max N₀ (max N₁ (k+2)),?_⟩
  intro δ hδ hδ₁ hGap V _ D hOrder hIn hOut
  let n := Fintype.card V
  have hn : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let b := (n:ℝ)/K
  have hb : 0 < b := div_pos hnR hK
  have hOne : 1 ≤ η*b := by
    have hN : (N₁:ℝ) ≤ n := by exact_mod_cast (show N₁ ≤ n by omega)
    have h := (div_le_iff₀ hη).mp (hN₁.trans hN)
    dsimp only [b]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hK).mpr
    linarith only [h]
  let P : V × Bool → Finset V := fun z =>
    univ.filter fun x => if z.2 then D.Adj z.1 x else D.Adj x z.1
  let size := balancedSize k n
  have hSz : ∀ i, (1-η)*b ≤ (size i:ℝ) ∧ (size i:ℝ) ≤ (1+η)*b := by
    intro i
    obtain ⟨hL,hU⟩ := balancedSize_bounds k n i
    change b-1 ≤ (size i:ℝ) at hL
    change (size i:ℝ) ≤ b+1 at hU
    exact ⟨by linarith only [hOne,hL], by linarith only [hOne,hU]⟩
  have hICard : Fintype.card (Fin (k+1)) < n^2 := by
    rw [Fintype.card_fin]
    have h := Nat.le_mul_self n
    nlinarith only [h, show k+2 ≤ n by omega]
  obtain ⟨rank,hRank⟩ := hSample P size (by omega) (balancedSize_sum k n)
    (by simp [Fintype.card_prod, mul_comm]) hICard
  have hDegreeProfile : ∀ z, (δ-η)*(n:ℝ) ≤ ((P z).card:ℝ) ∧
      ((P z).card:ℝ) ≤ (δ+η)*(n:ℝ) := by
    rintro ⟨v,d⟩
    cases d
    · simpa [P, inDegree, inNeighbours] using hIn v
    · simpa [P, outDegree] using hOut v
  have hCard : ∀ i, Fintype.card (Layer rank i) = size i := by
    intro i
    have hh := layer_card_filter rank i (fun _ => True)
    simpa using hh.trans (by simp [(hRank i).1])
  have hDeg : ∀ i z, (δ-4*η)*b ≤ ((slice rank i ∩ P z).card:ℝ) ∧
      ((slice rank i ∩ P z).card:ℝ) ≤ (δ+4*η)*b := by
    intro i z
    rcases hDegreeProfile z with ⟨hL,hU⟩
    have hControl := abs_lt.mp ((hRank i).2 z)
    have hE : (η/K)*(n:ℝ) = η*b := by dsimp only [b]; ring
    rw [hE] at hControl
    have hs : 0 ≤ (size i:ℝ)/(n:ℝ) := by positivity
    have hLo := mul_le_mul_of_nonneg_left hL hs
    have hHi := mul_le_mul_of_nonneg_left hU hs
    have hML : (size i:ℝ)/(n:ℝ)*((δ-η)*(n:ℝ)) = (δ-η)*(size i:ℝ) := by field_simp [hnR.ne']
    have hMU : (size i:ℝ)/(n:ℝ)*((δ+η)*(n:ℝ)) = (δ+η)*(size i:ℝ) := by field_simp [hnR.ne']
    rw [hML] at hLo
    rw [hMU] at hHi
    have hSize := hSz i
    have hδLo := mul_le_mul_of_nonneg_left hSize.1 hδ.le
    have hδHi := mul_le_mul_of_nonneg_left hSize.2 hδ.le
    have hη₁ : η ≤ 1 := by linarith only [hGap,hδ₁]
    have hTwo : (size i:ℝ) ≤ 2*b := by
      have hh := mul_le_mul_of_nonneg_right hη₁ hb.le
      nlinarith only [hh,hSize.2]
    have hηPay := mul_le_mul_of_nonneg_left hTwo hη.le
    have hδη := mul_le_mul_of_nonneg_right hδ₁ (mul_nonneg hη.le hb.le)
    constructor <;> nlinarith only [hControl.1,hControl.2,hLo,hHi,hδLo,hδHi,hηPay,hδη]
  obtain ⟨H,hSub,hCover,hCount⟩ := exists_cover_of_near_regular_layers D rank b δ η (4*η)
    hb hδ hδ₁ hη.le (by linarith only [hη]) hGap
    (fun i => by rw [hCard]; exact (hSz i).1)
    (fun i => by rw [hCard]; exact (hSz i).2)
    (fun i x => by
      have he := congrArg (fun v : ℕ => (v:ℝ))
        (layer_card_filter rank i.succ (fun y => D.Adj x.val y))
      exact (by simpa [P] using (hDeg i.succ (x.val,true)).1 :
        (δ-4*η)*b ≤ ((slice rank i.succ ∩ univ.filter (fun y => D.Adj x.val y)).card:ℝ)).trans he.ge)
    (fun i y => by
      have he := congrArg (fun v : ℕ => (v:ℝ))
        (layer_card_filter rank i.castSucc (fun x => D.Adj x y.val))
      exact he.le.trans (by simpa [P] using (hDeg i.castSucc (y.val,false)).2))
  refine ⟨H,hSub,hCover,hCount.trans_eq ?_⟩
  change (1+η)*b+(k:ℝ)*(η+3*(4*η)/δ)*b = (1+η+(k:ℝ)*(η+12*η/δ))*b
  ring

theorem exists_cover_of_almost_regular (k : ℕ) (δ η : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : 0 < η) (hGap : 4*η ≤ δ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V), N ≤ Fintype.card V →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
        (inDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ) ∧
        (outDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
        ((terminals H.Adj (univ : Finset V)).card:ℝ) ≤
          (1+η+(k:ℝ)*(η+12*η/δ))*((Fintype.card V:ℝ)/((k:ℝ)+1)) := by
  obtain ⟨N,hN⟩ := exists_cover_uniform_in_density.{u} k η hη
  exact ⟨N,hN δ hδ hδ₁ hGap⟩

/-- The input tolerance and order threshold can be fixed before the
host, for any desired upper fraction of components in the cover. -/
theorem exists_small_cover_uniform_in_density (d₀ ρ η : ℝ)
    (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η)
    (hGap : 8*η ≤ d₀) (hScale : 52*η ≤ ρ*d₀) :
    ∃ N : ℕ, ∀ (δ : ℝ), d₀ ≤ δ → δ ≤ 1 → ∀ {V : Type u} [Fintype V]
      (D : Digraph V), N ≤ Fintype.card V →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
        (inDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ) ∧
        (outDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
        ((terminals H.Adj (univ : Finset V)).card:ℝ) ≤ ρ*(Fintype.card V:ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_ge (4/ρ)
  obtain ⟨N,hN⟩ := exists_cover_uniform_in_density.{u} k η hη
  refine ⟨N,?_⟩
  intro δ hδ₀ hδ₁ V _ D hn hIn hOut
  have hδ := hd₀.trans_le hδ₀
  have hηρ : η ≤ ρ*δ/52 := by
    have he := mul_le_mul_of_nonneg_left hδ₀ hρ.le
    linarith only [hScale,he]
  obtain ⟨H,hHD,hCover,hCount⟩ := hN δ hδ hδ₁ (by linarith only [hη,hGap,hδ₀])
    D hn hIn hOut
  let K : ℝ := (k:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKρ : 1/K ≤ ρ/4 := by
    apply (div_le_iff₀ hK).mpr
    have he := (div_le_iff₀ hρ).mp hk
    dsimp [K]
    nlinarith only [he,hρ]
  have hηδ' : η ≤ η/δ := (le_div_iff₀ hδ).mpr (by
    calc
      η*δ ≤ η*1 := mul_le_mul_of_nonneg_left hδ₁ hη.le
      _ = η := mul_one _)
  have hRate : η+12*η/δ ≤ ρ/4 := by
    have he : 13*η/δ ≤ ρ/4 := (div_le_iff₀ hδ).mpr (by linarith only [hηρ])
    simp only [mul_div_assoc] at he ⊢
    linarith only [hηδ',he]
  have hCoeff : (1+η+(k:ℝ)*(η+12*η/δ))/K ≤ ρ := by
    have hLinear := mul_le_mul_of_nonneg_left hRate
      (show (0:ℝ) ≤ (k:ℝ) by positivity)
    have he := (div_le_iff₀ hK).mp hKρ
    dsimp [K] at he ⊢
    apply (div_le_iff₀ (show (0:ℝ) < (k:ℝ)+1 by positivity)).mpr
    nlinarith only [hRate,hLinear,he,hηδ',hρ,
      mul_nonneg hρ.le (show (0:ℝ) ≤ (k:ℝ) by positivity),
      div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) hη.le) hδ.le]
  refine ⟨H,hHD,hCover,hCount.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hCoeff (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  dsimp [K] at hh
  convert hh using 1
  ring

theorem exists_spanning_cover_with_small_path_count (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
      (D : Digraph V), N ≤ Fintype.card V →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
        (inDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      (∀ v, (δ-η)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ) ∧
        (outDegree D v:ℝ) ≤ (δ+η)*(Fintype.card V:ℝ)) →
      ∃ H : Digraph V, H ≤ D ∧ Nonempty (Cover H.Adj univ) ∧
        ((terminals H.Adj (univ : Finset V)).card:ℝ) ≤ ρ*(Fintype.card V:ℝ) := by
  let η := min (δ/8) (ρ*δ/52)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hGap : 8*η ≤ δ := by
    have h : η ≤ δ/8 := min_le_left _ _
    linarith only [h]
  have hScale : 52*η ≤ ρ*δ := by
    have h : η ≤ ρ*δ/52 := min_le_right _ _
    linarith only [h]
  obtain ⟨N,hN⟩ := exists_small_cover_uniform_in_density.{u} δ ρ η hδ hρ hη hGap hScale
  exact ⟨η,hη,N,hN δ le_rfl hδ₁⟩

/-- Concrete integral block sizes for the reserve partition. Every block
has at least half its equal-share order, and its complement has at least
a quarter of the host order. -/
theorem exists_balanced_reserve_sizes (k n : ℕ) (hn : 4*(k+2) ≤ n) :
    ∃ size : Fin (k+2) → ℕ, (∑ i,size i) = n ∧
      ∀ i, (n:ℝ)/(2*((k:ℝ)+2)) ≤ (size i:ℝ) ∧ (n:ℝ)/4 ≤ ((n-size i:ℕ):ℝ) := by
  let size : Fin (k+2) → ℕ := balancedSize (k+1) n
  refine ⟨size,balancedSize_sum _ _,?_⟩
  intro i
  have hb := balancedSize_bounds (k+1) n i
  push_cast at hb
  have hReal : 4*((k:ℝ)+2) ≤ (n:ℝ) := by exact_mod_cast hn
  have hk : (0:ℝ) < (k:ℝ)+2 := by positivity
  have hn₈ : (8:ℝ) ≤ n := by nlinarith only [hReal,Nat.cast_nonneg (α := ℝ) k]
  have h₄ : (4:ℝ) ≤ (n:ℝ)/((k:ℝ)+2) := (le_div_iff₀ hk).mpr hReal
  have hHalf : (n:ℝ)/((k:ℝ)+2) ≤ (n:ℝ)/2 := by
    apply (div_le_iff₀ hk).mpr
    have hp := mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)/2) (Nat.cast_nonneg (α := ℝ) k)
    nlinarith only [hp]
  have hnSize : size i ≤ n := by
    rw [← balancedSize_sum (k+1) n]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  change (n:ℝ)/(2*((k:ℝ)+2)) ≤ (size i:ℝ) ∧ (n:ℝ)/4 ≤ ((n-size i:ℕ):ℝ)
  rw [Nat.cast_sub hnSize, mul_comm (2:ℝ) (↑k+2),div_mul_eq_div_div]
  have he : (↑k+1+1:ℝ) = (k:ℝ)+2 := by ring
  rw [he] at hb
  change (n:ℝ)/((k:ℝ)+2)-1 ≤ (size i:ℝ) ∧
    (size i:ℝ) ≤ (n:ℝ)/((k:ℝ)+2)+1 at hb
  constructor <;> linarith only [hb.1,hb.2,h₄,hHalf,hn₈]

end OverfullWork.AdjacentLayerPathCover
