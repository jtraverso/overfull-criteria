module

public import OverfullWork.UniformSeedParameters

@[expose] public section


/-! # Unconditional uniform factorization for each fixed multiplicity budget -/
namespace OverfullWork.Gate8H2
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000
universe u

theorem factorization_of_uniform_parameters {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (x y : V) (hxy : x≠y) (j b c m D r : ℕ)
    (hb : 1≤b) (hc : 1000*(2^j+b+1)≤c) (hr : 1≤r) (hrm : r≤m)
    (hsmall : 1000*c*c*((4*2^j+2)*(r+1))≤m)
    (hsize : 30*(m:ℝ)^4*(((2^j:ℕ):ℝ)*(j+3:ℕ))^6<(r:ℝ)^6)
    (hcard : Fintype.card V=2*m) (hreg : M.IsRegularOfDegree D)
    (hmu : ∀ e,M.mult e≤2^j) (hbudget : M.HasParallelBudget x b)
    (hcontrol : M.CentreControl x b) (hD : D≤2*m) (hdense : (c+64)*m≤c*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  have hp : 1≤2^j:=Nat.one_le_pow j 2 (by omega)
  have hc1000 : 1000≤c:=by omega
  have hcpos : 0<c:=by omega
  have hm : 1≤m:=by omega
  have hmd : m≤D := by
    apply Nat.le_of_mul_le_mul_left (c:=c) ?_ hcpos
    nlinarith only [hdense,Nat.zero_le m]
  let t:=(4*2^j+2)*(r+1)
  let k:=D/2+(2*2^j-1)*r+2^j
  have hs : 2*2^j-1+1=2*2^j:=by omega
  have ht : 0<t:=by dsimp [t];positivity
  have hkt : k≤D/2+t:=by dsimp [k,t];nlinarith only [hp,hs]
  have htseed : 2*((2*2^j)*(r+1))+2≤t:=by dsimp [t];nlinarith only [hr]
  have hnum:=BoundedMargins.budget_of_density (2^j) b c m D t k hc ht hsmall hdense hkt
  obtain ⟨hpartition,hpalette⟩:=binary_moments_of_strong_moment j m D r hm hrm hD hsize
  exact M.factorization_of_binary_moments x y hxy j m D r t c b
    (ScaledMargins.degreeBound c m) hm hr hb hcpos hcard hreg hmu hbudget hcontrol hmd
    hpartition hpalette htseed hnum

/-- The order threshold depends only on the three fixed integer
parameters; it precedes the type, graph, centre, and regular degree. -/
theorem exists_uniform_factorization_threshold (j b c : ℕ)
    (hb : 1≤b) (hc : 1000*(2^j+b+1)≤c) :
    ∃ m₀ : ℕ,∀ m : ℕ,m₀≤m → ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (M : MultiGraph W) (x y : W),x≠y → ∀ D : ℕ,
      Fintype.card W=2*m → M.IsRegularOfDegree D →
      (∀ e,M.mult e≤2^j) → M.HasParallelBudget x b → M.CentreControl x b →
      D≤2*m → (c+64)*m≤c*D → ∃ C : M.EdgeColoring D,C.IsFactorization := by
  have hp : 1≤2^j:=Nat.one_le_pow j 2 (by omega)
  obtain ⟨m₀,hm₀⟩:=exists_uniform_parameters j c (by omega)
  refine ⟨m₀,?_⟩
  intro m hm W _ _ M x y hxy D hcard hreg hmu hbudget hcontrol hD hdense
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=hm₀ m hm
  exact factorization_of_uniform_parameters M x y hxy j b c m D r hb hc hr hrm hsmall hsize
    hcard hreg hmu hbudget hcontrol hD hdense

end OverfullWork.Gate8H2
