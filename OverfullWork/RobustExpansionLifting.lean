module

public import OverfullWork.RobustExpansionFinite

@[expose] public section


/-! # Robust expansion survives a bounded set of added vertices

All parameters are integer thresholds. No colouring or factorization
theorem is assumed. The robust-neighbour threshold pays for the added
vertices, and the admissible set-size margin is enlarged accordingly.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isRobustAt_of_induced (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (r r' t : ℕ)
    (hrobust : IsRobustAt (G.induce (S : Set V)) r t)
    (hbudget : Fintype.card V-S.card+r'≤r) :
    IsRobustAt G r' (t+(Fintype.card V-S.card)) := by
  intro A hAlo hAhi
  let k:=Fintype.card V-S.card
  let T : Finset (S : Set V):=univ.filter fun v => v.val∈A
  have hTimg : T.image Subtype.val=A∩S := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩:=mem_image.mp hx
      exact mem_inter.mpr ⟨(mem_filter.mp hv).2,v.property⟩
    · intro hx
      obtain ⟨hxA,hxS⟩:=mem_inter.mp hx
      exact mem_image.mpr ⟨⟨x,hxS⟩,mem_filter.mpr ⟨mem_univ _,hxA⟩,rfl⟩
  have hTcard : T.card=(A∩S).card := by
    rw [←hTimg,card_image_of_injective _ Subtype.val_injective]
  have hSle:=card_le_univ S
  have hinterle : T.card≤A.card:=by rw [hTcard];exact card_le_card inter_subset_left
  have hcut : (A\S).card≤k := by
    have hs : A\S⊆Sᶜ:=by intro x hx;exact mem_compl.mpr (mem_sdiff.mp hx).2
    have hh:=card_le_card hs
    simpa only [card_compl,card_univ,k] using hh
  have hsplit:=card_sdiff_add_card_inter A S
  have hAcard : A.card≤T.card+k:=by omega
  have hTlo : t≤T.card:=by change t+k≤A.card at hAlo;omega
  have hThi : T.card+t≤Fintype.card (S : Set V) := by
    have hScard : Fintype.card (S : Set V)=S.card:=by simp
    rw [hScard]
    change A.card+(t+k)≤Fintype.card V at hAhi
    dsimp only [k] at hAhi hAcard
    omega
  have hRN:=hrobust T hTlo hThi
  have himage : (neighbourhood (G.induce (S : Set V)) r T).image Subtype.val⊆
      neighbourhood G r' A := by
    intro x hx
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hx
    have hvN : r≤neighboursIn (G.induce (S : Set V)) T v := (mem_filter.mp hv).2
    have hcopy:=copy_neighboursIn_le (Copy.induce G (S : Set V)) T v
    have hsub : T.image (Copy.induce G (S : Set V))⊆A := by
      change T.image Subtype.val⊆A
      rw [hTimg]
      exact inter_subset_left
    have hmono:=neighboursIn_mono G hsub v.val
    have hbound : r≤neighboursIn G A v.val:=hvN.trans (hcopy.trans hmono)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hcount:=card_le_card himage
  rw [card_image_of_injective _ Subtype.val_injective] at hcount
  change A.card+r'≤(neighbourhood G r' A).card
  change k+r'≤r at hbudget
  omega

end OverfullWork.RobustExpansion
