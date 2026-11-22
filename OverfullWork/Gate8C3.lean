module

public import OverfullWork.DenseStarInternalCover

@[expose] public section


set_option maxRecDepth 4096

/-! # Gate 8C3: constructed internal covers and the asymptotic gap-two case

The order threshold below is uniform over all finite vertex types. The
argument permits controlled perturbations of the initial colour classes;
every uncovered internal copy is absorbed in the second palette.
-/

namespace OverfullWork.MultigraphExtension
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct the actual regular internal cover from G, with a fully
numerical finite size condition. The cover is a conclusion of the proof. -/
theorem exists_point_regular_internal_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m r : ℕ) (hr : 1≤r) (hrm : r≤m) (hsmall : 1000*(8*r+10)≤m)
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree)
    (hsize : 30*(m:ℝ)^4<(r:ℝ)^6) :
    ∃ (L : Finset (Option V)) (H : MultiGraph (Option V)) (q : ℕ),
      L.card=m ∧ Lᶜ.card=m ∧ none∈L ∧ some y∉L ∧
      q<G.maxDegree ∧ (∀ e,H.mult e≤(pointExtension G).mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈L ↔ v∈L) → H.mult s(u,v)=(pointExtension G).mult s(u,v) := by
  obtain ⟨L,k,C,hL,hB,hx,hy,hk,_,hbal,_,hvertex,_,hcol⟩:=exists_point_efficient_seed G y m r hr hrm
    hcard hgap hsat hdense hsize
  have hn : 1≤Fintype.card V:=Fintype.card_pos_iff.mpr ⟨y⟩
  obtain ⟨H,q,hq,hsub,hH,hC,hcover⟩:=(pointExtension G).exists_dense_star_internal_cover L none
    m G.maxDegree (8*r+10) k (by omega) hsmall hL hB hx
    (regular_of_saturated G hn hsat) (multiplicity_le_two G hgap)
    ((pointExtension G).parallelBudget_of_star none (pointExtension_isStarAt G) (multiplicity_le_two G hgap))
    (by omega) (by omega) C hbal
    (fun v => by have hh:=hvertex v; omega) hcol
  exact ⟨L,H,q,hL,hB,hx,hy,hq,hsub,hH,hC,hcover⟩

/-- The finite parameter version, using the constructed cover and the
unconditional bipartite residual factorization of gate 8C1. -/
theorem edgeColourable_saturated_gap_two_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m r : ℕ) (hr : 1≤r) (hrm : r≤m) (hsmall : 1000*(8*r+10)≤m)
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree)
    (hsize : 30*(m:ℝ)^4<(r:ℝ)^6) : G.EdgeColorable G.maxDegree := by
  obtain ⟨L,H,q,_,_,_,_,hq,hsub,hH,hC,hcover⟩:=exists_point_regular_internal_cover G y m r hr hrm
    hsmall hcard hgap hsat hdense hsize
  exact edgeColourable_of_internal_cover G H L q (Fintype.card_pos_iff.mpr ⟨y⟩) hsat hq hsub hH hC hcover

end OverfullWork.MultigraphExtension

namespace OverfullWork.Gate8C3
open SimpleGraph
open scoped Classical

/-- A deliberately coarse explicit order threshold. The error budget is
small enough for both matching perturbation and sequential absorption. -/
theorem explicit_seed_parameters (m : ℕ) (hm : 10000000000000≤m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 1000*(8*r+10)≤m ∧ 30*(m:ℝ)^4<(r:ℝ)^6 := by
  let r:=m/10000+1
  have hr : 1≤r:=by dsimp [r]; omega
  have hrsmall : 10000*r≤m+10000:=by dsimp [r]; omega
  have hrlarge : m<10000*r:=by dsimp [r]; omega
  have hmR : (10000000000000:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have hbase : 30*(m:ℝ)^4<((m:ℝ)/10000)^6 := by
    have hp : (0:ℝ)<(m:ℝ)^4:=by positivity
    have hconst : (30:ℝ)*10000^6<(10000000000000:ℝ)^2:=by norm_num
    have hsq:=hconst.trans_le (pow_le_pow_left₀ (by norm_num) hmR 2)
    have hmul:=mul_lt_mul_of_pos_right hsq hp
    rw [div_pow,lt_div_iff₀ (show (0:ℝ)<10000^6 by positivity)]
    convert hmul using 1 <;> ring
  have hreal : (m:ℝ)/10000≤(r:ℝ) := by
    have hh : (m:ℝ)<10000*(r:ℝ):=by exact_mod_cast hrlarge
    linarith
  have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/10000 by positivity) hreal 6
  exact ⟨r,hr,by omega,by omega,hbase.trans_le hpow⟩

/-- Explicit closure of the internal-cover obligation, uniformly over
finite graphs. The initial colour classes and H are both constructed. -/
theorem exists_internal_cover_explicit (m : ℕ) (hm : 10000000000000≤m)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    ∃ (L : Finset (Option V)) (H : MultiGraph (Option V)) (q : ℕ),
      L.card=m ∧ Lᶜ.card=m ∧ none∈L ∧ q<G.maxDegree ∧
      (∀ e,H.mult e≤(MultigraphExtension.pointExtension G).mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈L ↔ v∈L) → H.mult s(u,v)=(MultigraphExtension.pointExtension G).mult s(u,v) := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=explicit_seed_parameters m hm
  have hn : 0<Fintype.card V:=by omega
  obtain ⟨y⟩:=Fintype.card_pos_iff.mp hn
  obtain ⟨L,H,q,hL,hB,hx,_,hq,hsub,hH,hC,hcover⟩:=
    MultigraphExtension.exists_point_regular_internal_cover G y m r hr hrm hsmall
      hcard hgap hsat hdense hsize
  exact ⟨L,H,q,hL,hB,hx,hq,hsub,hH,hC,hcover⟩

/-- A concrete finite threshold for the dense saturated degree-gap-two family. -/
theorem edgeColourable_explicit (m : ℕ) (hm : 10000000000000≤m)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  obtain ⟨L,H,q,_,_,_,hq,hsub,hH,hC,hcover⟩:=exists_internal_cover_explicit m hm G hcard hgap hsat hdense
  have hn : 1≤Fintype.card V:=by omega
  exact MultigraphExtension.edgeColourable_of_internal_cover G H L q hn hsat hq hsub hH hC hcover

/-- A uniform asymptotic theorem. The threshold precedes the vertex type
and G; it cannot be chosen above the order of a previously fixed graph. -/
theorem eventually_dense_saturated_gap_two :
    ∃ m₀ : ℕ,∀ (m : ℕ),m₀≤m → ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V+1=2*m → G.maxDegree-G.minDegree≤2 →
      2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1) →
      6*(Fintype.card V+1)≤7*G.maxDegree → G.EdgeColorable G.maxDegree := by
  exact ⟨10000000000000,fun m hm _ _ _ G _ hc hg hs hd =>
    edgeColourable_explicit m hm G hc hg hs hd⟩

end OverfullWork.Gate8C3
