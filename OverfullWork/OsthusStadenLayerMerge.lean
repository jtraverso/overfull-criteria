module

public import OverfullWork.OsthusStadenRotationCoordinates

@[expose] public section


/-! Finish §5.11 for one prepared physical layer: the bridge and cut
configuration produces a pack of Hamilton cycles on the original host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe ue ui uw up

structure LayerBridgeData {E : Type ue} {I : Type ui} {W : Type uw} [Fintype W]
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (P : Type up) where
  φ : Equiv.Perm P
  project : I → P
  primaryCycle : Equiv.Perm P
  routing : RedArcRouting σ incoming outgoing A
  separated : ∀ u ∈ outgoing, σ u ∉ incoming
  spacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j → (σ^j) (a:I) = (b:I) → p ≤ j
  orbit : ∀ x y, σ.SameCycle x y ↔ φ.SameCycle (project x) (project y)
  redPrimary : ∀ u, ∃ a : ↥(incoming ∪ outgoing),
    φ.SameCycle (project (shadowSend σ incoming outgoing a)) u
  primarySpanning : ∀ u v, primaryCycle.SameCycle u v
  bridges : ∀ u, ∃ (e : E) (a b : ↥(incoming ∪ outgoing)),
    φ.SameCycle (project (shadowSend σ incoming outgoing a)) u ∧
    φ.SameCycle (project (shadowReceive σ incoming outgoing b)) (primaryCycle u) ∧
    (∀ x, (x,Sum.inl e) ∈ A → x ∈ sliceCell (shadowSend σ incoming outgoing a)) ∧
    (∀ x, (Sum.inl e,x) ∈ A → x ∈ sliceCell (shadowReceive σ incoming outgoing b))

/-- All factors of one physical layer are merged in disjoint rotation
families. The H3 arcs and the old factor arcs remain in the host. -/
theorem exists_hamilton_pack_of_prepared_layer
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) :
    ∃ N : ℕ,
      ∀ {E : Type ue} [Fintype E] {I : Type ui} [Fintype I] {W : Type uw} [Fintype W]
      {P : Type up} [Fintype P] (σ : Equiv.Perm I) (incoming outgoing : Finset I)
      (p κ m : ℕ) (A : Finset (SliceVertex E I W × SliceVertex E I W))
      (L : LayerBridgeData σ incoming outgoing p A P)
      (root : ↥(incoming ∪ outgoing)) (F : Fin κ → Equiv.Perm (SliceVertex E I W))
      (H : I → Digraph W) (G : Digraph (SliceVertex E I W)) (ε₀ d₀ : ℝ),
      κ ≤ (p-4)*m →
      (∀ f, UsesSliceArcs σ A (F f)) →
      (∀ f g, f ≠ g → ∀ x, F f x ≠ F g x) →
      (∀ f x, G.Adj x (F f x)) →
      (∀ i x y, (H i).Adj x y → G.Adj (.inr (i,x)) (.inr (σ i,y))) →
      (∀ i x y f, (H i).Adj x y → F f (.inr (i,x)) ≠ .inr (σ i,y)) →
      (∀ i, IsCentredSuperregular (H i) ε₀ d₀) →
      0 ≤ ε₀ → ε₀ ≤ ε → d ≤ d₀-2*ε₀ →
      0 < Fintype.card W → N ≤ Fintype.card W →
      (m:ℝ)+ν*(Fintype.card W:ℝ) ≤ d*τ*(Fintype.card W:ℝ) →
      γ*(Fintype.card W:ℝ)+(m:ℝ) ≤ d*(Fintype.card W:ℝ) →
      ∃ F' : Fin κ → Equiv.Perm (SliceVertex E I W),
        (∀ f, HasSpanningCycle (fun x y => F' f x = y)) ∧
        (∀ f x, G.Adj x (F' f x)) ∧
        ∀ f g, f ≠ g → ∀ x, F' f x ≠ F' g x := by
  obtain ⟨N,hN⟩ := exists_indexed_hamilton_batch.{max ue ui uw,ui}
    d ε ν τ γ hν hWidth hε.le hτγ hγ hd
  refine ⟨N,?_⟩
  intro E _ I _ W _ P _ σ incoming outgoing p κ m A L root F H G ε₀ d₀ hCap
    hUse hDis hHost hH3 hFresh hReg hε₀ hE hD hW hn hCost hDegree
  obtain ⟨batch,_,_,hCount⟩ := exists_factor_batch_schedule κ (p-4) m hCap
  let R := ↥(incoming ∪ outgoing)
  let col (q : Fin (p-4)) (a : R) := (σ^(2+q.val)) (shadowSend σ incoming outgoing a)
  let cut (q : Fin (p-4)) (a : R) := sliceCell (E := E) (W := W) (col q a)
  let B (q : Fin (p-4)) := ((univ : Finset (Fin κ)).filter (fun f => batch f = q))
  have hB (q : Fin (p-4)) : Fintype.card (B q) ≤ m := by
    rw [Fintype.card_coe]
    exact hCount q
  have hCutDis (qa qb : R × Fin (p-4)) (h : qa ≠ qb) :
      Disjoint (cut qa.2 qa.1) (cut qb.2 qb.1) :=
    disjoint_black_cut_cells σ incoming outgoing p L.separated L.spacing qa qb h
  have hBlock (q : Fin (p-4)) : ∃ ρ : B q → Equiv.Perm (SliceVertex E I W),
      (∀ f, HasSpanningCycle (fun x y => ρ f x = y)) ∧
      (∀ f g, f ≠ g → ∀ x, ρ f x ≠ ρ g x) ∧
      (∀ f x, (∀ a, x ∉ cut q a) → ρ f x = F f x) ∧
      ∀ f a (x : cut q a), ∃ w y, x.val = .inr (col q a,w) ∧
        ρ f x.val = .inr (σ (col q a),y) ∧ (H (col q a)).Adj w y := by
    let e := Fintype.equivFin (B q)
    let Fb := fun f => F (e.symm f).val
    have hMatch (a : R) (f : Fin (Fintype.card (B q))) :
        (sliceCell (col q a)).image (Fb f) = sliceCell (σ (col q a)) := by
      have hBlack := black_after_red_pair σ incoming outgoing p L.spacing a (2+q.val)
        (by omega) (by have := q.isLt; omega)
      exact factor_black_successor_matching σ A _ _ (hUse _) (fun x hx => L.routing.black _ hBlack x hx _)
    let D := rotationReserveOfPairs σ Fb (col q) H hMatch
    have hc : (Fintype.card (B q):ℝ) ≤ (m:ℝ) := by exact_mod_cast hB q
    have hm := rotationReserveOfPairs_margins σ Fb (col q) H hMatch d ε ν τ γ ε₀ d₀ N
      hReg hε₀ hε hW hE hD hn (by linarith only [hc,hCost]) (by linarith only [hc,hDegree])
    obtain ⟨rel,hConn,hRel⟩ := exists_common_cut_links σ L.φ L.project L.primaryCycle
      incoming outgoing p A L.routing L.separated L.spacing L.orbit L.redPrimary L.primarySpanning L.bridges q
    obtain ⟨ρ,hCycle,hρDis,hKeep,hNew⟩ := hN Fb (cut q) D rel root hm
      (fun f g h => hDis _ _ (fun he => h (e.symm.injective (Subtype.ext he))))
      (fun a b h => hCutDis (a,q) (b,q) (fun he => h (congrArg Prod.fst he)))
      (hConn root) (fun f => (hRel _ (hUse (e.symm f).val)).1)
      (fun f => (hRel _ (hUse (e.symm f).val)).2)
    refine ⟨fun f => ρ (e f),fun f => hCycle _,fun f g h => hρDis _ _ (fun he => h (e.injective he)),?_,?_⟩
    · intro f x hx
      simpa only [Fb,e.symm_apply_apply] using hKeep (e f) x hx
    · intro f a x
      obtain ⟨M,hM,hArc⟩ := hNew a
      let t := (sliceCellEquiv (E := E) (W := W) (col q a)).symm
      have hx : (Sum.inr (col q a,t x) : SliceVertex E I W) = x.val := by
        rw [←sliceCellEquiv_val]
        exact congrArg Subtype.val ((sliceCellEquiv (E := E) (W := W) (col q a)).apply_symm_apply x)
      exact ⟨t x,t (M (e f) x),hx.symm,hArc (e f) x,hM (e f) x⟩
  choose ρ hCycle hρDis hKeep hNew using hBlock
  let asBlock (f : Fin κ) (q : Fin (p-4)) (h : batch f = q) : B q :=
    ⟨f,mem_filter.mpr ⟨mem_univ _,h⟩⟩
  let F' (f : Fin κ) := ρ (batch f) (asBlock f (batch f) rfl)
  have hReindex (f : Fin κ) (q : Fin (p-4)) (h : batch f = q) :
      F' f = ρ q (asBlock f q h) := by subst q; rfl
  refine ⟨F',fun f => hCycle _ _,?_,?_⟩
  · intro f x
    by_cases h : ∃ a, x ∈ cut (batch f) a
    · obtain ⟨a,ha⟩ := h
      obtain ⟨w,y,hx,hy,hEdge⟩ := hNew _ (asBlock f _ rfl) a ⟨x,ha⟩
      change x = _ at hx
      change F' f x = _ at hy
      rw [hy,hx]
      exact hH3 _ _ _ hEdge
    · have he : F' f x = F f x := hKeep _ (asBlock f _ rfl) x (fun a ha => h ⟨a,ha⟩)
      rw [he]
      exact hHost f x
  · intro f g hfg x he
    by_cases hSame : batch f = batch g
    · rw [hReindex f (batch g) hSame] at he
      exact hρDis (batch g) _ _ (fun hh => hfg (congrArg Subtype.val hh)) x he
    have hMixed (f g : Fin κ) (hb : batch f ≠ batch g) (hEq : F' f x = F' g x)
        (hx : ∃ a, x ∈ cut (batch f) a) : False := by
      obtain ⟨a,ha⟩ := hx
      have hg (b : R) : x ∉ cut (batch g) b :=
        fun h => disjoint_left.mp (hCutDis (a,batch f) (b,batch g)
          (fun hh => hb (congrArg Prod.snd hh))) ha h
      obtain ⟨w,y,hx,hy,hEdge⟩ := hNew _ (asBlock f _ rfl) a ⟨x,ha⟩
      change x = _ at hx
      change F' f x = _ at hy
      have he' : F' g x = F g x := hKeep _ (asBlock g _ rfl) x hg
      rw [he'] at hEq
      exact hFresh _ _ _ g hEdge (by rw [←hx,←hEq,hy])
    by_cases hf : ∃ a, x ∈ cut (batch f) a
    · exact hMixed f g hSame he hf
    by_cases hg : ∃ a, x ∈ cut (batch g) a
    · exact hMixed g f (Ne.symm hSame) he.symm hg
    exact hDis f g hfg x
      ((hKeep _ (asBlock f _ rfl) x (fun a ha => hf ⟨a,ha⟩)).symm.trans
        (he.trans (hKeep _ (asBlock g _ rfl) x (fun a ha => hg ⟨a,ha⟩))))

end OverfullWork.DirectedRobustExpansion
