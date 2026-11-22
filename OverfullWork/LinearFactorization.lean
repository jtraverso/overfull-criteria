module

public import OverfullWork.LinearSeedParameters
public import OverfullWork.DeterministicSeed
public import OverfullWork.SupportExcessPartition
public import OverfullWork.WeightedCentreCompletion

@[expose] public section


/-! # Linear-scale factorization from an actual deterministic additive seed

The pairing adapts to the centre, and weighted centre-first completion
handles its large excess without assuming the final factorization.
-/
namespace OverfullWork.Gate8J2I
open SimpleGraph MultiGraph
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linear_centre_factorization (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (C S h b m D : ℕ) (hC : 4000≤C) (hS : 1≤S)
    (hcapLo : S≤4^h) (hcap : 4^h≤4*S) (hbS : b≤S)
    (hsize : linearHalfBound C S≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4^h)
    (hbudget : M.HasParallelBudget x b) (hcontrol : M.CentreControl x b)
    (hD : D≤2*m) (hdense : (C+64)*m≤C*D) :
    ∃ F : M.EdgeColoring D,F.IsFactorization := by
  obtain ⟨r,hr,hrm,h4S,hsmall,hmoment⟩:=linear_seed_parameters C S m hC hS hsize
  have hSr : S<r:=by omega
  have hm : 1≤m:=by omega
  have hmd : m≤D := by
    apply Nat.le_of_mul_le_mul_left (c:=C) ?_ (by omega)
    nlinarith only [hdense,Nat.zero_le m]
  obtain ⟨L,hL,hSc,hx,_,hdis⟩:=M.exists_support_excess_degree_partition_center x y hxy
    m b S r hm hcard hbudget hbS hS hcontrol hSr hmoment
  let t:=64*r
  have ht : 0<t:=by dsimp [t];positivity
  have hμr : 4^h≤r:=by omega
  have hbt : b≤t:=by dsimp [t];omega
  obtain ⟨k,A,hk,hkm,hbal,heq,hv,_,hcol⟩:=M.exists_deterministic_internal_seed L
    h m D r hr hL hSc hreg hmu hμr hmd hdis
  have hk' : k≤D/2+t:=hk
  have hkpos : 0<k:=by omega
  have hDk : D≤4*k:=by omega
  have hW : 4^h≤t:=by dsimp [t];omega
  have hnum:=ScaledMargins.budget_of_density C m D (2*t) k (by omega) (by omega)
    hsmall hdense (by omega)
  exact M.factorization_of_weighted_centre_seed L x m D t C k b (4^h)
    (by omega) ht hbt hW hnum hsmall hmd hk' hkpos hDk hL hSc hx hreg hbudget
    (fun z _ => hmu s(x,z)) A hbal heq hv hcol

end OverfullWork.Gate8J2I
