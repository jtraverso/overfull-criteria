module

/-
# Pegado por listas: interfaz suficiente, condicionada

Adaptado del archivo `smwaqvcjl/m7/PegadoFlex.lean` del ZIP de traspaso.
Las pruebas de pegado se conservan; se corrige el umbral a `3 * Δ > n`
y se elimina la atribución no comprobada de la hipótesis de descomposición
a un teorema de GGKLO. Este módulo no demuestra la conjetura Overfull.

Pregunta del PEGADO: `G` se parte en bloques `G₁,…,Gₘ` (aristas disjuntas,
unión de aristas `= E(G)`), cada bloque es `Δ`-coloreable. ¿Se pueden PEGAR
las coloraciones en una coloración propia de `G`?

La forma fuerte (`GluingStrong`) pide que las coloraciones de los bloques
sean ya compatibles en los vértices compartidos. Aquí se estudia una
condición suficiente alternativa: **se pide que cada bloque
sea FLEXIBLE**, es decir, que se pueda colorear no sólo con colores
libres, sino desde *listas prescritas* de colores permitidos por arista.

Contenido:
* `usedAt f v`   : colores que una coloración parcial `f` usa en `v`.
* `ProperOn f`   : `f` es propia donde está definida.
* `SupportBelow b i f` : `f` colorea EXACTAMENTE las aristas de bloques `< i`.
* `earlierDeg b i v` / `blockDeg b i v` : grados de interfaz.
* `BlockExtension b sz k` : cada bloque colorea desde cualquier lista de
  tamaño `≥ sz`.
* `edgeColorable_of_blockExtension` (TEOREMA PRINCIPAL): si (a) cada bloque
  es `sz`-flexible y (b) las listas que produce el pegado (complemento de
  los colores ya usados en los DOS extremos) tienen tamaño `≥ sz`, entonces
  `G` es `k`-coloreable por aristas. Sin hipótesis de compatibilidad global.
* `edgeColorable_of_degree_interface` : corolario en grados: basta
  `(grados previos en los extremos) + sz e ≤ k`.
* `blockExtension_of_matching` : instancia para bloques emparejamiento.
* `OverfullDecompositionHypothesis` : hipótesis abierta suficiente para
  la dirección difícil de la conjetura; no se afirma que esté publicada.
-/
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Choose

@[expose] public section


set_option maxHeartbeats 1000000

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Coloración de aristas (mismas definiciones que `Overfull.lean`) -/

/-- Una coloración propia de aristas de `G` con colores en `α` es una
coloración propia del grafo de línea. -/
abbrev EdgeColoring (α : Type*) := G.lineGraph.Coloring α

/-- `G` admite una coloración propia de aristas con `n` colores: `χ'(G) ≤ n`. -/
def EdgeColorable (n : ℕ) : Prop := G.lineGraph.Colorable n

/-! ## Coloraciones parciales de aristas

Trabajamos con funciones `G.edgeSet → Option (Fin k)`: `none` = arista aún
sin colorear. Así el estado del pegado secuencial no cambia de tipo al
avanzar de bloque, y la inducción sobre `i` es una recursión corriente.
-/

/-- Colores que la coloración parcial `f` usa en el vértice `v`. -/
noncomputable def usedAt {k : ℕ} (f : G.edgeSet → Option (Fin k)) (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun c => ∃ e : G.edgeSet, f e = some c ∧ v ∈ (e : Sym2 V))

/-- `f` es propia allí donde está definida: dos aristas adyacentes no
reciben el mismo color. -/
def ProperOn {k : ℕ} (f : G.edgeSet → Option (Fin k)) : Prop :=
  ∀ (e₁ e₂ : G.edgeSet) (c : Fin k), G.lineGraph.Adj e₁ e₂ →
    f e₁ = some c → f e₂ = some c → False

/-- `f` colorea exactamente las aristas de bloques `< i` (según `b`). -/
def SupportBelow {m k : ℕ} (b : G.edgeSet → Fin m) (i : ℕ)
    (f : G.edgeSet → Option (Fin k)) : Prop :=
  ∀ e : G.edgeSet, (f e).isSome ↔ (b e).val < i

/-- Número de aristas de bloques `< i` incidentes con `v`. -/
noncomputable def earlierDeg {m : ℕ} (b : G.edgeSet → Fin m) (i : ℕ) (v : V) : ℕ :=
  (Finset.univ.filter (fun e : G.edgeSet => (b e).val < i ∧ v ∈ (e : Sym2 V))).card

/-- Número de aristas del bloque `i` incidentes con `v`. -/
noncomputable def blockDeg {m : ℕ} (b : G.edgeSet → Fin m) (i : Fin m) (v : V) : ℕ :=
  (Finset.univ.filter (fun e : G.edgeSet => b e = i ∧ v ∈ (e : Sym2 V))).card

/-! ## Lema de conteo: los colores usados en `v` no superan el grado previo -/

/-- Las aristas coloreadas por `f` incidentes con `v`. -/
noncomputable def coloredAt {k : ℕ} (f : G.edgeSet → Option (Fin k)) (v : V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e : G.edgeSet => (f e).isSome ∧ v ∈ (e : Sym2 V))

theorem usedAt_card_le_coloredAt_card {k : ℕ} (f : G.edgeSet → Option (Fin k)) (v : V) :
    (usedAt f v).card ≤ (coloredAt f v).card := by
  classical
  have key : ∀ (c : Fin k), c ∈ usedAt f v → ∃ e : G.edgeSet, e ∈ coloredAt f v ∧ f e = some c := by
    intro c hc
    simp only [usedAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨e, he, hv⟩ := hc
    refine ⟨e, ?_, he⟩
    simp only [coloredAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [he]; rfl, hv⟩
  let g : {c : Fin k // c ∈ usedAt f v} → {e : G.edgeSet // e ∈ coloredAt f v} :=
    fun c => ⟨Classical.choose (key c.1 c.2), (Classical.choose_spec (key c.1 c.2)).1⟩
  have hinj : Function.Injective g := by
    intro c c' hcc
    have h1 : f (g c).1 = some c.1 := (Classical.choose_spec (key c.1 c.2)).2
    have h2 : f (g c').1 = some c'.1 := (Classical.choose_spec (key c'.1 c'.2)).2
    have hval : (g c).1 = (g c').1 := by rw [hcc]
    rw [hval] at h1
    have : some c.1 = some c'.1 := by rw [← h1, ← h2]
    exact Subtype.ext (Option.some.inj this)
  have hcard := Fintype.card_le_of_injective g hinj
  simpa using hcard

/-- **Conteo de la interfaz.** En una coloración parcial que cubre exactamente
los bloques anteriores a `i`, el número de colores usados en `v` es a lo sumo
el número de aristas de esos bloques que inciden en `v`. Esto es lo que hace
que el "espacio" en el vértice se traduzca en listas grandes. -/
theorem usedAt_card_le_earlierDeg {m k : ℕ} {b : G.edgeSet → Fin m} {i : ℕ}
    {f : G.edgeSet → Option (Fin k)} (h : SupportBelow b i f) (v : V) :
    (usedAt f v).card ≤ earlierDeg b i v := by
  classical
  refine (usedAt_card_le_coloredAt_card f v).trans (Finset.card_le_card ?_)
  intro e he
  simp only [coloredAt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨(h e).mp he.1, he.2⟩


/-! ## La hipótesis de flexibilidad por bloques -/

/-- **Un bloque es `sz`-flexible**: para cualquier asignación de listas
permitidas `L` con `|L e| ≥ sz i e`, hay una coloración propia del bloque
usando sólo colores de `L`.

Es una hipótesis sobre todas las listas del tamaño indicado. Su obtención
para bloques concretos necesita una prueba independiente; aquí no se
deduce de expansión robusta ni de un resultado externo. -/
def BlockExtension {m : ℕ} (b : G.edgeSet → Fin m) (sz : Fin m → G.edgeSet → ℕ)
    (k : ℕ) : Prop :=
  ∀ (i : Fin m) (L : {e : G.edgeSet // b e = i} → Finset (Fin k)),
    (∀ e, sz i e.val ≤ (L e).card) →
    ∃ g : {e : G.edgeSet // b e = i} → Fin k,
      (∀ e, g e ∈ L e) ∧
      (∀ (e₁ e₂ : {e : G.edgeSet // b e = i}), e₁ ≠ e₂ →
        G.lineGraph.Adj e₁.val e₂.val → g e₁ ≠ g e₂)

/-- La lista de colores que el pegado deja disponibles para la arista `e`:
todos los colores menos los ya usados en algún extremo de `e`. -/
noncomputable def freeList {k : ℕ} (f : G.edgeSet → Option (Fin k)) (e : G.edgeSet) :
    Finset (Fin k) :=
  Finset.univ \ ((e : Sym2 V).toFinset.biUnion (fun v => usedAt f v))

theorem mem_freeList_iff {k : ℕ} (f : G.edgeSet → Option (Fin k)) (e : G.edgeSet)
    (c : Fin k) :
    c ∈ freeList f e ↔ ∀ v : V, v ∈ (e : Sym2 V) → c ∉ usedAt f v := by
  classical
  constructor
  · intro hc v hv hcon
    exact (Finset.mem_sdiff.mp hc).2
      (Finset.mem_biUnion.mpr ⟨v, by simpa using hv, hcon⟩)
  · intro hc
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hcon
    obtain ⟨v, hv, hcu⟩ := Finset.mem_biUnion.mp hcon
    exact hc v (by simpa using hv) hcu

/-- **TEOREMA PRINCIPAL DEL PEGADO POR LISTAS.** Si los bloques cubren las
aristas, cada bloque es flexible (`BlockExtension`) y las listas que produce
el pegado son al menos `sz`, entonces `G` es `k`-coloreable por aristas.

No se pide compatibilidad alguna entre las coloraciones de los bloques: la
compatibilidad se **construye** bloque a bloque, porque cada bloque se
colorea desde las listas que dejan libres los bloques anteriores. -/
theorem edgeColorable_of_blockExtension {m : ℕ} (b : G.edgeSet → Fin m)
    (sz : Fin m → G.edgeSet → ℕ) (k : ℕ) (hflex : BlockExtension (G := G) b sz k)
    (hsize : ∀ (i : Fin m) (f : G.edgeSet → Option (Fin k)), SupportBelow b i.val f →
      ∀ e : {e : G.edgeSet // b e = i}, sz i e.val ≤ (freeList f e.val).card) :
    G.EdgeColorable k := by
  classical
  -- Inducción: existe un estado que colorea exactamente los bloques `< i`
  -- y es propio.
  have key : ∀ i : ℕ, i ≤ m → ∃ f : G.edgeSet → Option (Fin k),
      SupportBelow b i f ∧ ProperOn f := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => none, ?_, ?_⟩
      · intro e
        simp
      · intro e₁ e₂ c _ h
        exact nomatch h
    | succ i ih =>
      intro hi
      obtain ⟨f, hsupp, hprop⟩ := ih (by omega)
      by_cases hlt : i < m
      · -- colorear el bloque `i`
        obtain ⟨g, hgL, hgprop⟩ :=
          hflex ⟨i, hlt⟩ (fun e => freeList f e.val) (hsize ⟨i, hlt⟩ f hsupp)
        -- `hfresh`: un color elegido para una arista nueva no está usado
        -- por una arista vieja en un extremo común.
        have hfresh : ∀ (en eo : G.edgeSet) (hb : b en = ⟨i, hlt⟩) (c : Fin k),
            g ⟨en, hb⟩ = c → f eo = some c → ∀ v : V,
            v ∈ (en : Sym2 V) → v ∈ (eo : Sym2 V) → False := by
          intro en eo hb c hgc hfc v hvn hvo
          have hmem : c ∈ freeList f en := by
            rw [← hgc]; exact hgL ⟨en, hb⟩
          have hbim : c ∈ (en : Sym2 V).toFinset.biUnion (fun w => usedAt f w) :=
            Finset.mem_biUnion.mpr ⟨v, by simpa using hvn, by
              simp only [usedAt, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨eo, hfc, hvo⟩⟩
          exact (Finset.mem_sdiff.mp hmem).2 hbim
        let f' : G.edgeSet → Option (Fin k) := fun e =>
          if h : b e = ⟨i, hlt⟩ then some (g ⟨e, h⟩) else f e
        refine ⟨f', ?_, ?_⟩
        · -- invariante de soporte
          intro e
          by_cases h : b e = ⟨i, hlt⟩
          · have hv : (b e).val = i := by rw [h]
            rw [hv]
            simp [f', h]
          · have hv : (b e).val ≠ i := fun hc => h (Fin.ext hc)
            have hs := hsupp e
            simp only [f', dif_neg h]
            rw [hs]
            omega
        · -- properness preservada
          intro e₁ e₂ c hadj h1 h2
          by_cases hb1 : b e₁ = ⟨i, hlt⟩ <;> by_cases hb2 : b e₂ = ⟨i, hlt⟩
          · -- ambas en el bloque nuevo
            have h1' : g ⟨e₁, hb1⟩ = c := by simpa [f', hb1] using h1
            have h2' : g ⟨e₂, hb2⟩ = c := by simpa [f', hb2] using h2
            exact hgprop ⟨e₁, hb1⟩ ⟨e₂, hb2⟩
              (fun hh => hadj.1 (congrArg Subtype.val hh)) hadj (by rw [h1', h2'])
          · -- `e₁` nuevo, `e₂` viejo
            have h1' : g ⟨e₁, hb1⟩ = c := by simpa [f', hb1] using h1
            have h2' : f e₂ = some c := by simpa [f', hb2] using h2
            obtain ⟨v, hv1, hv2⟩ := (lineGraph_adj_iff_exists.mp hadj).2
            exact hfresh e₁ e₂ hb1 c h1' h2' v hv1 hv2
          · -- `e₁` viejo, `e₂` nuevo
            have h2' : g ⟨e₂, hb2⟩ = c := by simpa [f', hb2] using h2
            have h1' : f e₁ = some c := by simpa [f', hb1] using h1
            obtain ⟨v, hv1, hv2⟩ := (lineGraph_adj_iff_exists.mp hadj).2
            exact hfresh e₂ e₁ hb2 c h2' h1' v hv2 hv1
          · -- ambas viejas
            have h1' : f e₁ = some c := by simpa [f', hb1] using h1
            have h2' : f e₂ = some c := by simpa [f', hb2] using h2
            exact hprop e₁ e₂ c hadj h1' h2'
      · -- no hay bloque `i`: el estado no cambia
        refine ⟨f, ?_, hprop⟩
        intro e
        have h1 : (b e).val < i := by
          have := (b e).isLt
          omega
        rw [hsupp e]
        omega
  -- extraer la coloración global
  obtain ⟨f, hsupp, hprop⟩ := key m le_rfl
  have hall : ∀ e : G.edgeSet, ∃ c : Fin k, f e = some c := by
    intro e
    have hlt : (b e).val < m := (b e).isLt
    have := (hsupp e).mpr hlt
    exact Option.isSome_iff_exists.mp this
  choose cc hcc using hall
  refine ⟨⟨cc, ?_⟩⟩
  intro e₁ e₂ hadj hEq
  exact hprop e₁ e₂ (cc e₁) hadj (hcc e₁) (by rw [hcc e₂, hEq])

/-! ## Corolario en grados de interfaz (la forma utilizable) -/

/-- **Corolario en grados.** Si cada bloque es `sz`-flexible y para cada arista
`e` del bloque `i` la suma de los grados *previos* en sus dos extremos más
`sz e` no pasa de `k`, entonces `G` es `k`-coloreable por aristas.

El término `∑_{v ∈ e} earlierDeg b i v` es exactamente "cuántos colores
pueden estar ya prohibidos en los extremos de `e` al llegar al bloque `i`":
es una cota del tamaño de la interfaz. Una descomposición propuesta debe
justificar esta cota; aquí no se deduce de ninguna propiedad de expansión. -/
theorem edgeColorable_of_degree_interface {m : ℕ} (b : G.edgeSet → Fin m)
    (sz : Fin m → G.edgeSet → ℕ) (k : ℕ) (hflex : BlockExtension (G := G) b sz k)
    (hint : ∀ (i : Fin m) (e : G.edgeSet), b e = i →
      (∑ v ∈ (e : Sym2 V).toFinset, earlierDeg b i.val v) + sz i e ≤ k) :
    G.EdgeColorable k := by
  classical
  refine edgeColorable_of_blockExtension b sz k hflex ?_
  intro i f hsupp e
  have hbim : ((e.val : Sym2 V).toFinset.biUnion (fun v => usedAt f v)).card
      ≤ ∑ v ∈ (e.val : Sym2 V).toFinset, earlierDeg b i.val v := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
    intro v _
    exact usedAt_card_le_earlierDeg hsupp v
  have hcard : (freeList f e.val).card
      = k - ((e.val : Sym2 V).toFinset.biUnion (fun v => usedAt f v)).card := by
    simp [freeList, Finset.card_sdiff]
  have h := hint i e.val e.property
  omega

/-! ## Una instancia no vacía de la flexibilidad: bloques emparejamiento -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Si un bloque es un emparejamiento (dos aristas suyas nunca son adyacentes),
es flexible con listas de tamaño `1`: basta elegir un color permitido por arista
y no hay conflictos internos que respetar. -/
theorem blockExtension_of_matching {m : ℕ} (b : G.edgeSet → Fin m)
    (hmatch : ∀ (i : Fin m) (e₁ e₂ : {e : G.edgeSet // b e = i}), e₁ ≠ e₂ →
      ¬ G.lineGraph.Adj e₁.val e₂.val) (k : ℕ) :
    BlockExtension (G := G) b (fun _ _ => 1) k := by
  classical
  intro i L hL
  have hne : ∀ e : {e : G.edgeSet // b e = i}, (L e).Nonempty := by
    intro e
    have h1 : 1 ≤ (L e).card := hL e
    exact Finset.card_pos.mp (by omega)
  choose g hg using hne
  exact ⟨g, hg, fun e₁ e₂ hne' hadj => absurd hadj (hmatch i e₁ e₂ hne')⟩

/-- Pegado de bloques que son emparejamientos. -/
theorem edgeColorable_of_matching_blocks {m : ℕ} (b : G.edgeSet → Fin m)
    (hmatch : ∀ (i : Fin m) (e₁ e₂ : {e : G.edgeSet // b e = i}), e₁ ≠ e₂ →
      ¬ G.lineGraph.Adj e₁.val e₂.val) (k : ℕ)
    (hint : ∀ (i : Fin m) (e : G.edgeSet), b e = i →
      (∑ v ∈ (e : Sym2 V).toFinset, earlierDeg b i.val v) + 1 ≤ k) :
    G.EdgeColorable k :=
  edgeColorable_of_degree_interface b (fun _ _ => 1) k
    (blockExtension_of_matching b hmatch k) hint

/-! ## Hipótesis abierta de descomposición

La propiedad siguiente es suficiente para la dirección difícil de la
conjetura. No se demuestra ni se identifica con un lema publicado.
En particular, no basta una descomposición en expansores: hacen falta
`BlockExtension` y las cotas de listas con los cuantificadores indicados.
La desigualdad `3 * Δ > n` es estricta; el módulo `Boundary` certifica
que reemplazarla por `≥` hace falsa la conclusión.
-/

/-- Certificado abstracto de pegado, sin exigencia geométrica sobre los bloques. -/
def HasColouringDecomposition (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ m : ℕ, ∃ b : G.edgeSet → Fin m, ∃ sz : Fin m → G.edgeSet → ℕ,
    BlockExtension (G := G) b sz k ∧
    (∀ (i : Fin m) (f : G.edgeSet → Option (Fin k)),
      SupportBelow b i.val f →
      ∀ e : {e : G.edgeSet // b e = i}, sz i e.val ≤ (freeList f e.val).card)

/-- Sin restricciones adicionales sobre los bloques, el certificado es
equivalente a la coloreabilidad. La vuelta usa un solo bloque y listas
iguales a la paleta completa; no aporta una descomposición estructural. -/
theorem hasColouringDecomposition_iff (k : ℕ) :
    G.HasColouringDecomposition k ↔ G.EdgeColorable k := by
  classical
  constructor
  · rintro ⟨m, b, sz, hflex, hsize⟩
    exact edgeColorable_of_blockExtension b sz k hflex hsize
  · rintro ⟨C⟩
    refine ⟨1, (fun _ => 0), (fun _ _ => k), ?_, ?_⟩
    · intro i L hL
      refine ⟨(fun e => C e.val), ?_, ?_⟩
      · intro e
        have heq : L e = univ := (L e).eq_univ_of_card (by
          have hle := (L e).card_le_univ
          have hge := hL e
          change k ≤ (L e).card at hge
          simp only [Fintype.card_fin] at hle ⊢
          omega)
        rw [heq]
        exact mem_univ _
      · intro e₁ e₂ _ hadj
        exact C.valid hadj
    · intro i f hsupp e
      have hi : i.val = 0 := by omega
      have hf : ∀ a, f a = none := by
        intro a
        cases hfa : f a with
        | none => rfl
        | some c =>
          have h := (hsupp a).mp (by simp [hfa])
          change (0 : ℕ) < i.val at h
          omega
      have hempty : ∀ v : V, usedAt f v = ∅ := by
        intro v
        ext c
        simp [usedAt, hf]
      have hfree : freeList f e.val = univ := by
        ext c
        simp [freeList, mem_biUnion, hempty]
      rw [hfree]
      simp

/-- `G` contiene un subgrafo inducido `Δ(G)`-overfull:
`|E(G[s])| > Δ(G)·⌊|s|/2⌋` para algún `s`. -/
def HasOverfullSubgraph : Prop :=
  ∃ s : Finset V, G.maxDegree * (s.card / 2) <
    (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card

/-- Hipótesis suficiente, todavía no demostrada: para `3 * Δ > n`, existe
una obstrucción overfull o una descomposición que satisface el pegado. -/
def OverfullDecompositionHypothesis (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
    3 * G'.maxDegree > Fintype.card V →
      G'.HasOverfullSubgraph ∨
      G'.HasColouringDecomposition G'.maxDegree

/-- Auditoría lógica: la hipótesis abstracta ya contiene toda la dirección
difícil de la conjetura, no sólo un lema de expansión. -/
theorem overfullDecompositionHypothesis_iff :
    OverfullDecompositionHypothesis V ↔
      ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
        3 * G'.maxDegree > Fintype.card V →
        ¬ G'.HasOverfullSubgraph → G'.EdgeColorable G'.maxDegree := by
  constructor
  · intro h G' _ hdeg hno
    rcases h G' hdeg with hof | hcert
    · exact (hno hof).elim
    · exact (hasColouringDecomposition_iff G'.maxDegree).mp hcert
  · intro h G' _ hdeg
    by_cases hof : G'.HasOverfullSubgraph
    · exact Or.inl hof
    · exact Or.inr ((hasColouringDecomposition_iff G'.maxDegree).mpr (h G' hdeg hof))

/-- Consecuencia condicionada a `OverfullDecompositionHypothesis`. -/
theorem hasOverfullSubgraph_of_not_edgeColorable
    (hdecomp : OverfullDecompositionHypothesis V)
    (hΔ : 3 * G.maxDegree > Fintype.card V) (h2 : ¬ G.EdgeColorable G.maxDegree) :
    G.HasOverfullSubgraph := by
  have h := hdecomp G hΔ
  rcases h with hof | ⟨m, b, sz, hflex, hsize⟩
  · exact hof
  · exact absurd (edgeColorable_of_blockExtension b sz G.maxDegree hflex hsize) h2

/-- Dirección difícil de la conjetura, bajo la hipótesis de descomposición. -/
theorem edgeColorable_of_decomposition (hdecomp : OverfullDecompositionHypothesis V)
    (hΔ : 3 * G.maxDegree > Fintype.card V) (hof : ¬ G.HasOverfullSubgraph) :
    G.EdgeColorable G.maxDegree := by
  by_contra h2
  exact hof (hasOverfullSubgraph_of_not_edgeColorable hdecomp hΔ h2)

/-- **Instancia voraz.** Si los bloques son aristas sueltas (es decir `b` es
inyectiva: el orden en que se colorean las aristas), el pegado es exactamente
la coloración voraz: basta que en cada paso quede al menos un color libre.
En particular el marco reproduce el teorema clásico "voraz": si al llegar a
cada arista los colores ya usados en sus dos extremos no agotan la paleta,
`G` es `k`-coloreable. -/
theorem edgeColorable_of_singleton_blocks {m : ℕ} (b : G.edgeSet → Fin m)
    (hinj : Function.Injective b) (k : ℕ)
    (hint : ∀ (i : Fin m) (e : G.edgeSet), b e = i →
      (∑ v ∈ (e : Sym2 V).toFinset, earlierDeg b i.val v) + 1 ≤ k) :
    G.EdgeColorable k :=
  edgeColorable_of_matching_blocks b
    (fun i e₁ e₂ hne => by
      have hb : b e₁.val = b e₂.val := by rw [e₁.property, e₂.property]
      exact fun _ => hne (Subtype.ext (hinj hb))) k hint

/-! ## Resumen de axiomas -/

#print axioms SimpleGraph.usedAt_card_le_earlierDeg
#print axioms SimpleGraph.edgeColorable_of_blockExtension
#print axioms SimpleGraph.edgeColorable_of_degree_interface
#print axioms SimpleGraph.blockExtension_of_matching
#print axioms SimpleGraph.edgeColorable_of_matching_blocks
#print axioms SimpleGraph.hasOverfullSubgraph_of_not_edgeColorable
#print axioms SimpleGraph.edgeColorable_of_decomposition
#print axioms SimpleGraph.edgeColorable_of_singleton_blocks
#print axioms SimpleGraph.hasColouringDecomposition_iff
#print axioms SimpleGraph.overfullDecompositionHypothesis_iff


/-! ## La pieza que falta (enunciado exacto, sin `sorry`)

**Lema voraz de listas.** Para cualquier conjunto finito de aristas `F` y
listas `L` con `|L e| ≥ d_F(u) + d_F(v) − 1` en toda `e = uv ∈ F` (donde
`d_F(x)` cuenta las aristas de `F` que inciden en `x`), existe una coloración
propia de `F` con `C e ∈ L e`.

Estrategia de la prueba (inducción sobre `F`): se aparta `e₀ = u₀v₀ ∈ F`, se
colora `F \ {e₀}` por hipótesis de inducción, y los colores prohibidos para
`e₀` son a lo sumo `d_{F∖{e₀}}(u₀) + d_{F∖{e₀}}(v₀) ≤ |L e₀| − 1` (los usados
en cada extremo están en biyección con las aristas ya coloreadas allí). De ahí
`BlockExtension b (fun i e => d_{bloque i}(u) + d_{bloque i}(v) − 1) k`, que
junto con `edgeColorable_of_degree_interface` da un teorema de pegado **sin
ninguna hipótesis abstracta**:

  `(Σ_{v ∈ e} earlierDeg v) + (Σ_{v ∈ e} blockDeg v) − 1 ≤ k` ⟹ `G` clase 1.

Es la formalización pendiente; el resto de la cadena ya está probado arriba.
-/

end SimpleGraph
