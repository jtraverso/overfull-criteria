module

public import OverfullWork.LayeredPairedBacktracking

@[expose] public section


/-! # The two endpoint closures of the CMS alternating path

A paired route has 2n+1 edges. Adding a free edge at each endpoint gives
2n+3; the other parity uses one extra matching pair and gives 2n+5.
The displayed constants count actual graph edges, without identifying
the number of growth rounds with the path length.
-/
namespace OverfullWork.PairedRoutes.Route
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}
set_option maxHeartbeats 16000000

def close (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b : V) (hStart : F.Adj a p.first) (hEnd : F.Adj (τ z) b) : (F ⊔ K).Walk a b :=
  Walk.cons (Or.inl hStart) ((p.toWalk K hK).concat (Or.inl hEnd))

theorem support_close (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b : V) (hStart : F.Adj a p.first) (hEnd : F.Adj (τ z) b) :
    (p.close K hK a b hStart hEnd).support=a :: (p.vertices ++ [b]) := by
  simp only [close,Walk.support_cons,Walk.support_concat,p.support_toWalk K hK]

theorem length_close (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b : V) (hStart : F.Adj a p.first) (hEnd : F.Adj (τ z) b) :
    (p.close K hK a b hStart hEnd).length=2*n+3 := by
  simp only [close,Walk.length_cons,Walk.length_concat,p.length_toWalk K hK]

theorem close_isPath (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b : V) (hStart : F.Adj a p.first) (hEnd : F.Adj (τ z) b)
    (hp : p.vertices.Nodup) (ha : a ∉ p.vertices) (hb : b ∉ p.vertices) (hab : a ≠ b) :
    (p.close K hK a b hStart hEnd).IsPath := by
  rw [Walk.isPath_def,p.support_close K hK a b hStart hEnd]
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · apply hp.append (by simp)
    apply List.disjoint_left.mpr
    intro v hv hvb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hvb
    exact hb (hvb ▸ hv)

def closeExtra (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b y : V) (hy : y ∈ U) (hStart : F.Adj a p.first)
    (hEnd : F.Adj (τ z) (τ y)) (hLast : F.Adj y b) : (F ⊔ K).Walk a b :=
  Walk.cons (Or.inl hStart)
    ((((p.toWalk K hK).concat (Or.inl hEnd)).concat (Or.inr (hK y hy).symm)).concat (Or.inl hLast))

theorem support_closeExtra (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b y : V) (hy : y ∈ U) (hStart : F.Adj a p.first)
    (hEnd : F.Adj (τ z) (τ y)) (hLast : F.Adj y b) :
    (p.closeExtra K hK a b y hy hStart hEnd hLast).support=a :: (p.vertices ++ [τ y,y,b]) := by
  simp only [closeExtra,Walk.support_cons,Walk.support_concat,p.support_toWalk K hK,
    List.append_assoc,List.cons_append,List.nil_append]

theorem length_closeExtra (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b y : V) (hy : y ∈ U) (hStart : F.Adj a p.first)
    (hEnd : F.Adj (τ z) (τ y)) (hLast : F.Adj y b) :
    (p.closeExtra K hK a b y hy hStart hEnd hLast).length=2*n+5 := by
  simp only [closeExtra,Walk.length_cons,Walk.length_concat,p.length_toWalk K hK]

theorem closeExtra_isPath (p : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b y : V) (hy : y ∈ U) (hStart : F.Adj a p.first)
    (hEnd : F.Adj (τ z) (τ y)) (hLast : F.Adj y b)
    (hp : p.vertices.Nodup) (hAvoid : ∀ v ∈ p.vertices, v ∉ ({a,b,y,τ y}:Finset V))
    (hab : a ≠ b) (hay : a ≠ y) (haτ : a ≠ τ y) (hby : b ≠ y)
    (hbτ : b ≠ τ y) (hyτ : y ≠ τ y) :
    (p.closeExtra K hK a b y hy hStart hEnd hLast).IsPath := by
  rw [Walk.isPath_def,p.support_closeExtra K hK a b y hy hStart hEnd hLast]
  have hOut : ∀ v ∈ ({a,b,y,τ y}:Finset V), v ∉ p.vertices := by
    intro v hv hpv
    exact hAvoid v hpv hv
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    have ha := hOut a (by simp)
    tauto
  · apply hp.append
    · simp [Ne.symm,hby,hbτ,hyτ]
    · apply List.disjoint_left.mpr
      intro v hv hvTail
      have hn := hAvoid v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hvTail
      rcases hvTail with hvTail|hvTail|hvTail <;> subst v <;> exact hn (by simp)

end OverfullWork.PairedRoutes.Route

namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Retain the roles of every edge through the paired-route data.
Mapping a walk into the ambient graph must not discard this certificate. -/
def AlternatingCertificate (τ : Equiv.Perm V) (F K : SimpleGraph V) (U : Finset V)
    (a b : V) (xs : List V) : Prop :=
  (∀ x ∈ U, K.Adj x (τ x)) ∧
    ((∃ (z : V) (n : ℕ) (r : Route τ F U z n),
        F.Adj a r.first ∧ F.Adj (τ z) b ∧ xs=a :: (r.vertices ++ [b])) ∨
     (∃ (z y : V) (n : ℕ) (r : Route τ F U z n), y ∈ U ∧
        F.Adj a r.first ∧ F.Adj (τ z) (τ y) ∧ F.Adj y b ∧ xs=a :: (r.vertices ++ [τ y,y,b])))

theorem Route.close_certificate {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}
    (r : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b : V) (hStart : F.Adj a r.first) (hEnd : F.Adj (τ z) b) :
    AlternatingCertificate τ F K U a b (r.close K hK a b hStart hEnd).support :=
  ⟨hK,Or.inl ⟨z,n,r,hStart,hEnd,r.support_close K hK a b hStart hEnd⟩⟩

theorem Route.closeExtra_certificate {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}
    (r : Route τ F U z n) (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (a b y : V) (hy : y ∈ U) (hStart : F.Adj a r.first)
    (hEnd : F.Adj (τ z) (τ y)) (hLast : F.Adj y b) :
    AlternatingCertificate τ F K U a b (r.closeExtra K hK a b y hy hStart hEnd hLast).support :=
  ⟨hK,Or.inr ⟨z,y,n,r,hy,hStart,hEnd,hLast,r.support_closeExtra K hK a b y hy hStart hEnd hLast⟩⟩

end OverfullWork.PairedRoutes
