module

public import OverfullWork.OsthusStadenCoreException
public import OverfullWork.OsthusStadenExceptionalPhaseSlots

@[expose] public section


/-! Assign the split of Claim 5.3 to the layers that request each base half. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- Split the core-to-half arcs and assign the pieces to requests.
Pieces for different requests are disjoint, with a lower degree at
the core endpoint and an upper degree at the ordinary endpoint. -/
theorem exists_core_exception_phase_pieces (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {J L : Type*}
      (G : Digraph V) (Z : Finset V) (half : J → Finset V) (requests : J → Finset L),
      N ≤ Fintype.card V →
      (∀ i j, i ≠ j → Disjoint (half i) (half j)) →
      (∀ i, Nonempty (↥(requests i) ↪ Fin k)) →
      ∃ pieces : L → J → Digraph V,
        (∀ l i x y, (pieces l i).Adj x y → l ∈ requests i ∧ G.Adj x y ∧ x ∈ Z ∧ y ∈ half i) ∧
        (∀ l i l' i', (l,i) ≠ (l',i') → Disjoint (pieces l i) (pieces l' i')) ∧
        (∀ l i, l ∈ requests i → ∀ x ∈ Z,
          profileCount (half i) (outProfile G x)/(k:ℝ)-ε*(Fintype.card V:ℝ) ≤ (outDegree (pieces l i) x:ℝ)) ∧
        ∀ l i, l ∈ requests i → ∀ y ∈ half i,
          (inDegree (pieces l i) y:ℝ) ≤ profileCount Z (inProfile G y)/(k:ℝ)+ε*(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := exists_exceptional_pair_split.{u} ε hε k hk
  refine ⟨N,?_⟩
  intro V _ J L G Z half requests hSize hHalf hSlots
  choose bank hBank hBankDis hOut hIn using fun i => hN G Z (half i) hSize
  let slot (i : J) := Classical.choice (hSlots i)
  let pieces (l : L) (i : J) := if h : l ∈ requests i then bank i (slot i ⟨l,h⟩) else ⊥
  have hAdj (l : L) (i : J) (x y : V) (h : (pieces l i).Adj x y) :
      ∃ hReq : l ∈ requests i, (bank i (slot i ⟨l,hReq⟩)).Adj x y := by
    by_cases hl : l ∈ requests i
    · exact ⟨hl,by simpa only [pieces,dif_pos hl] using h⟩
    · have he : pieces l i = ⊥ := dif_neg hl
      rw [he] at h
      exact h.elim
  refine ⟨pieces,?_,?_,?_,?_⟩
  · intro l i x y h
    obtain ⟨hr,ha⟩ := hAdj l i x y h
    exact ⟨hr,hBank _ _ _ _ ha⟩
  · intro l i l' i' hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hl,hl'⟩
    obtain ⟨hr,ha⟩ := hAdj l i x y hl
    obtain ⟨hr',ha'⟩ := hAdj l' i' x y hl'
    by_cases hi : i = i'
    · subst i'
      have hs : slot i ⟨l,hr⟩ ≠ slot i ⟨l',hr'⟩ := by
        intro he
        exact hne (Prod.ext (congrArg Subtype.val ((slot i).injective he)) rfl)
      exact disjoint_iff_inf_le.mp (hBankDis i _ _ hs) ⟨ha,ha'⟩
    · exact disjoint_left.mp (hHalf i i' hi) (hBank _ _ _ _ ha).2.2 (hBank _ _ _ _ ha').2.2
  · intro l i hr x hx
    simpa only [pieces,dif_pos hr] using hOut i (slot i ⟨l,hr⟩) x hx
  · intro l i hr y hy
    simpa only [pieces,dif_pos hr] using hIn i (slot i ⟨l,hr⟩) y hy

end OverfullWork.DirectedRobustExpansion
