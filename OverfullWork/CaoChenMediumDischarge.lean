module

public import OverfullWork.CaoChenCorollary10

@[expose] public section


/-! # Concrete R1 discharge in the large high-neighbour-deficit case

The sources are actual S-neighbours of a partial colouring. Corollary 10
constructs their exceptional set; the remaining donations pay Delta.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteCounting CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- An actual exceptional family and its palette bounds suffice to pay
for the low vertex, without a charge hypothesis. -/
theorem charge_ge_of_exceptional_family (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (Q E : ℕ) (hQ : 1≤Q) (hDQ : Q≤G.maxDegree)
    (hεQ : (32:ℝ)≤ε^3*(Q:ℝ))
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hmass : 8*((E:ℝ)+1/ε)≤ε^2*(G.maxDegree:ℝ))
    (hdef : ε^2*(G.maxDegree:ℝ)/4<
      ((G.maxDegree-highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℕ):ℝ))
    (X : Finset V) (hX : X⊆neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y)
    (hXcard : X.card≤E)
    (hgood : ∀u∈neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y\X,
      Q*(badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card<G.maxDegree+Q) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let N:=neighboursS c q x y
  let A:=N\X
  let ρ:ℝ:=2/(Q:ℝ)
  have hQR : (0:ℝ)<(Q:ℝ) := by exact_mod_cast (show 0<Q by omega)
  have hDQR : (Q:ℝ)≤(G.maxDegree:ℝ) := by exact_mod_cast hDQ
  have hεsq : ε^2≤1 := by nlinarith
  have hεsqpos : 0<ε^2 := sq_pos_of_pos hε
  have hNS := neighboursS_card_gt_deficit_sub_ratio hG hcm ε hε hx
  have hcardN : A.card+X.card=N.card := by
    exact card_sdiff_add_card_eq_card hX
  have hcardNR : (A.card:ℝ)+(X.card:ℝ)=(N.card:ℝ) := by exact_mod_cast hcardN
  have hXcardR : (X.card:ℝ)≤(E:ℝ) := by exact_mod_cast hXcard
  have hratio : (1-ε)/ε≤1/ε :=
    div_le_div_of_nonneg_right (by linarith) hε.le
  have hA : ε^2*(G.maxDegree:ℝ)/8≤(A.card:ℝ) := by
    change _ < (N.card:ℝ) at hNS
    linarith
  have hεQlarge : (32:ℝ)≤ε*(Q:ℝ) := by
    have hm:=mul_le_mul_of_nonneg_right hεsq (show 0≤ε*(Q:ℝ) by positivity)
    nlinarith only [hm,hεQ]
  have hρ : 0<ρ := div_pos (by norm_num) hQR
  have hρε : ρ<ε := (div_lt_iff₀ hQR).mpr (by linarith)
  have hformula : (ε-ρ)/ρ=ε*(Q:ℝ)/2-1 := by
    dsimp [ρ]
    field_simp
  have hquota : 8/ε^2≤(ε-ρ)/ρ := by
    rw [hformula]
    apply (div_le_iff₀ hεsqpos).mpr
    nlinarith only [hεQ,hεsq]
  have hdon : ∀u∈A,8/ε^2≤donation G q u := by
    intro u hu
    have huN : u∈neighboursS c q x y := (mem_sdiff.mp hu).1
    have huAdj := (mem_neighborFinset G x u).mp (mem_filter.mp huN).1
    have hg := hgood u hu
    have hgR : (Q:ℝ)*((badColours c q u).card:ℝ)<(G.maxDegree:ℝ)+(Q:ℝ) := by
      exact_mod_cast hg
    have hb : ((badColours c q u).card:ℝ)≤ρ*(G.maxDegree:ℝ) := by
      dsimp [ρ]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hQR).mpr
      nlinarith only [hgR,hDQR]
    exact hquota.trans (donation_ge_of_badColours_card_fraction hcm ε ρ hρ hρε huAdj hx hb)
  have hsumgood : (A.card:ℝ)*(8/ε^2)≤∑u∈A,donation G q u := by
    simpa only [sum_const,nsmul_eq_mul] using
      (sum_le_sum (fun u hu => hdon u hu))
  have hpay : (G.maxDegree:ℝ)≤(A.card:ℝ)*(8/ε^2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hεsqpos).mpr
    nlinarith only [hA]
  have hAsub : A⊆G.neighborFinset x := by
    intro u hu
    exact (mem_filter.mp (mem_sdiff.mp hu).1).1
  have hsumAll : (∑u∈A,donation G q u)≤∑u∈G.neighborFinset x,donation G q u :=
    sum_le_sum_of_subset_of_nonneg hAsub (fun u _ _ => donation_nonnegative G q u)
  have hq : q≤(G.maxDegree:ℝ) := by
    dsimp [q]
    nlinarith [show 0≤ε*(G.maxDegree:ℝ) by positivity]
  rw [low_charge_formula G q x hx]
  have hd : (0:ℝ)≤(G.degree x:ℝ) := Nat.cast_nonneg _
  change q≤_
  linarith

/-- Published Case 2: Corollary 10 supplies the actual exceptional set;
a large high-neighbour deficit supplies enough remaining donors. -/
theorem charge_ge_of_large_high_count_deficit (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hcutoff : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (Q : ℕ) (hQ : 1≤Q) (hsize : (3*k+1)*Q*Q≤G.maxDegree)
    (hDQ : Q≤G.maxDegree) (hεQ : (32:ℝ)≤ε^3*(Q:ℝ))
    (hmass : 8*((((k+1)*(Q+1)^(3*k+1):ℕ):ℝ)+1/ε)≤ε^2*(G.maxDegree:ℝ))
    (hdef : ε^2*(G.maxDegree:ℝ)/4<
      ((G.maxDegree-highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℕ):ℝ)) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  obtain ⟨X,hX,hXcard,hgood⟩:=CaoChenCorollary10.exceptional_neighbours
    hG c hcm ε hε hεone k hk hx hscale hcutoff Q hQ hsize
  apply charge_ge_of_exceptional_family hG c hcm ε hε hεone Q
    ((k+1)*(Q+1)^(3*k+1)) hQ hDQ hεQ hx _ hdef X hX hXcard hgood
  exact hmass

end OverfullWork.CaoChenDischarging
