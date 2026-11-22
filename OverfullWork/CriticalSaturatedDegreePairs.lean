module

public import OverfullWork.CriticalDegreePairs
public import OverfullWork.TightDeficitSaturation

@[expose] public section


/-! # Transporting CCJS degree conflicts through saturated vertices

Ambient degrees can be used in CCJS only when they agree with the
degrees of the critical copy. Tight VAL budgets supply this agreement.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem copy_saturated_degree_pair_dichotomy (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (hactive : ∀x,0<H.degree x) {a z : W} (hne : z≠a)
    (ha : H.degree a=G.degree (f a)) (hz : H.degree z=G.degree (f z))
    (hlo : G.degree (f z)+G.degree (f a)≤G.maxDegree) :
    G.degree (f z)+G.maxDegree+5<Fintype.card V+2*G.degree (f a) := by
  have hv := Gate8J2C.critical_degree_dichotomy H hcrit hactive hne (by omega)
  have hc := Fintype.card_le_of_injective f f.injective
  omega

omit [DecidableEq V] in
/-- A forbidden ambient degree pair cannot occur with both endpoints
saturated inside a common-Delta critical copy. -/
theorem not_saturated_forbidden_degree_pair (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (hactive : ∀x,0<H.degree x) {a z : W} (hne : z≠a)
    (ha : H.degree a=G.degree (f a)) (hz : H.degree z=G.degree (f z))
    (hlo : G.degree (f z)+G.degree (f a)≤G.maxDegree)
    (hforbidden : Fintype.card V+2*G.degree (f a)≤G.degree (f z)+G.maxDegree+5) : False := by
  have hh := copy_saturated_degree_pair_dichotomy f hmax hcrit hactive hne ha hz hlo
  omega

/-- Tight deficits at two incident edges provide the two degree
equalities required to reject a forbidden CCJS pair. -/
theorem not_tight_forbidden_degree_pair (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (hactive : ∀x,0<H.degree x) (T : Finset V)
    (hT : ((univ : Finset W).filter fun x => H.degree x=H.maxDegree).image f⊆T)
    {b a c z : W} (hba : H.Adj b a) (hcz : H.Adj c z) (hne : z≠a)
    (hta : neighboursIn G T (f b)=G.maxDegree-G.degree (f a)+1)
    (htz : neighboursIn G T (f c)=G.maxDegree-G.degree (f z)+1)
    (hlo : G.degree (f z)+G.degree (f a)≤G.maxDegree)
    (hforbidden : Fintype.card V+2*G.degree (f a)≤G.degree (f z)+G.maxDegree+5) : False :=
  not_saturated_forbidden_degree_pair f hmax hcrit hactive hne
    (degree_eq_of_tight_deficit f hmax hcrit T hT hba hta)
    (degree_eq_of_tight_deficit f hmax hcrit T hT hcz htz) hlo hforbidden

end OverfullWork.EdgeKernel
