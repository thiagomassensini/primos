import Mathlib

/-!
# Structural persistence under changes of presentation

This module gives a neutral logical interface for the question:

> What remains unchanged when the representation changes?

The answer is deliberately typed.  Codes in two views need not be equal, and
their interior and boundary components need not agree separately.  What can be
transported without further hypotheses is:

* the semantic state recovered by a certified codec;
* a normalized readout that factors through that semantic state;
* the zero predicate of that readout;
* the total `interior + boundary` ledger;
* any observed distinction between two semantic states.

The interface does not assert that a codec exists for an arbitrary system.
Each application must construct its encoder, decoder, validity predicate, and
round-trip proof.  Likewise, the boundary ledger is supplied independently;
it may not be defined after the fact merely as `total - interior`.
-/

namespace CPFormal.Logic

universe uSemantic uCode uView uObs

/--
A lossless encoder/decoder on the image of an encoder.

No global `encode (decode code) = code` law is required.  That stronger
round-trip belongs only to applications whose valid code domain supports it.
-/
structure RestrictedCodec
    (Semantic : Type uSemantic) (Code : Type uCode) where
  Valid : Code → Prop
  encode : Semantic → Code
  decode : Code → Semantic
  valid_encode : ∀ semantic, Valid (encode semantic)
  decode_encode : ∀ semantic, decode (encode semantic) = semantic

namespace RestrictedCodec

variable {Semantic : Type uSemantic} {Code : Type uCode}

/-- Encoding and decoding preserves every semantic observable. -/
theorem observe_decode_encode
    (codec : RestrictedCodec Semantic Code)
    {Obs : Type uObs} (observe : Semantic → Obs)
    (semantic : Semantic) :
    observe (codec.decode (codec.encode semantic)) = observe semantic := by
  rw [codec.decode_encode]

end RestrictedCodec

/--
Several coded views of one semantic state with a shared normalized readout.

`ledger` records an independently supplied decomposition of each normalized
readout into interior and boundary contributions.
-/
structure ReadoutAtlas
    (View : Type uView) (Semantic : Type uSemantic) (Obs : Type uObs)
    [AddCommMonoid Obs] where
  Code : View → Type uCode
  codec : ∀ view, RestrictedCodec Semantic (Code view)
  semanticRead : Semantic → Obs
  normalizedRead : ∀ view, Code view → Obs
  read_valid :
    ∀ view code, (codec view).Valid code →
      normalizedRead view code =
        semanticRead ((codec view).decode code)
  interior : ∀ view, Code view → Obs
  boundary : ∀ view, Code view → Obs
  ledger :
    ∀ view code, (codec view).Valid code →
      normalizedRead view code =
        interior view code + boundary view code

namespace ReadoutAtlas

variable
    {View : Type uView} {Semantic : Type uSemantic} {Obs : Type uObs}
    [AddCommMonoid Obs]

/-- Canonical transport decodes one view and re-encodes the same semantic state. -/
def transport
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source) :
    atlas.Code target :=
  (atlas.codec target).encode ((atlas.codec source).decode code)

/-- Canonical transport always lands in the declared valid target domain. -/
theorem valid_transport
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source) :
    (atlas.codec target).Valid (atlas.transport source target code) := by
  exact
    (atlas.codec target).valid_encode
      ((atlas.codec source).decode code)

/-- A normalized readout of an encoded semantic state is the semantic readout. -/
theorem normalizedRead_encode
    (atlas : ReadoutAtlas View Semantic Obs)
    (view : View) (semantic : Semantic) :
    atlas.normalizedRead view ((atlas.codec view).encode semantic) =
      atlas.semanticRead semantic := by
  rw [atlas.read_valid view _ ((atlas.codec view).valid_encode semantic)]
  rw [(atlas.codec view).decode_encode semantic]

/--
The canonical transport preserves the normalized readout of every valid source
code.
-/
theorem normalizedRead_transport
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source)
    (hcode : (atlas.codec source).Valid code) :
    atlas.normalizedRead target (atlas.transport source target code) =
      atlas.normalizedRead source code := by
  calc
    atlas.normalizedRead target (atlas.transport source target code) =
        atlas.semanticRead ((atlas.codec source).decode code) := by
      simpa [transport] using
        atlas.normalizedRead_encode target
          ((atlas.codec source).decode code)
    _ = atlas.normalizedRead source code :=
      (atlas.read_valid source code hcode).symm

/-- Closing means only that the declared normalized readout is zero. -/
def Closes
    (atlas : ReadoutAtlas View Semantic Obs)
    (view : View) (code : atlas.Code view) : Prop :=
  atlas.normalizedRead view code = 0

/-- Canonical transport preserves and reflects closing of a valid code. -/
theorem closes_transport_iff
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source)
    (hcode : (atlas.codec source).Valid code) :
    atlas.Closes target (atlas.transport source target code) ↔
      atlas.Closes source code := by
  unfold Closes
  rw [atlas.normalizedRead_transport source target code hcode]

/--
Only the total interior-plus-boundary ledger is automatically transported.
No componentwise equality is asserted.
-/
theorem totalLedger_transport
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source)
    (hcode : (atlas.codec source).Valid code) :
    atlas.interior target (atlas.transport source target code) +
        atlas.boundary target (atlas.transport source target code) =
      atlas.interior source code + atlas.boundary source code := by
  rw [← atlas.ledger target _ (atlas.valid_transport source target code)]
  rw [atlas.normalizedRead_transport source target code hcode]
  exact atlas.ledger source code hcode

/--
Universal minimal view-invariance theorem.

It packages preservation of the readout, its zero predicate, and the complete
interior-plus-boundary ledger, while leaving the codes and the two ledger
components free to change.
-/
theorem minimal_view_invariance
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) (code : atlas.Code source)
    (hcode : (atlas.codec source).Valid code) :
    atlas.normalizedRead target (atlas.transport source target code) =
        atlas.normalizedRead source code ∧
      (atlas.Closes target (atlas.transport source target code) ↔
        atlas.Closes source code) ∧
      atlas.interior target (atlas.transport source target code) +
          atlas.boundary target (atlas.transport source target code) =
        atlas.interior source code + atlas.boundary source code := by
  exact
    ⟨atlas.normalizedRead_transport source target code hcode,
      atlas.closes_transport_iff source target code hcode,
      atlas.totalLedger_transport source target code hcode⟩

/--
Every valid view preserves a nontrivial semantic distinction seen by the
shared readout.
-/
theorem normalizedRead_encode_ne_of_semanticRead_ne
    (atlas : ReadoutAtlas View Semantic Obs)
    (view : View) {before after : Semantic}
    (hchange :
      atlas.semanticRead before ≠ atlas.semanticRead after) :
    atlas.normalizedRead view ((atlas.codec view).encode before) ≠
      atlas.normalizedRead view ((atlas.codec view).encode after) := by
  rw [atlas.normalizedRead_encode, atlas.normalizedRead_encode]
  exact hchange

end ReadoutAtlas

/--
A noncanonical transport with an explicit additive readout defect.

The defect may encode a boundary, omitted tail, gain mismatch, or cutoff
commutator.  It is data to be calculated, not silently discarded.
-/
structure ReadoutTransportWithDefect
    {View : Type uView} {Semantic : Type uSemantic} {Obs : Type uObs}
    [AddCommMonoid Obs]
    (atlas : ReadoutAtlas View Semantic Obs)
    (source target : View) where
  map : atlas.Code source → atlas.Code target
  defect : atlas.Code source → Obs
  read_map :
    ∀ code,
      atlas.normalizedRead target (map code) =
        atlas.normalizedRead source code + defect code

namespace ReadoutTransportWithDefect

variable
    {View : Type uView} {Semantic : Type uSemantic} {Obs : Type uObs}
    [AddCommMonoid Obs]
    {atlas : ReadoutAtlas View Semantic Obs}
    {source target : View}

/-- A vanishing explicit defect gives exact readout transport. -/
theorem read_eq_of_defect_eq_zero
    (transport : ReadoutTransportWithDefect atlas source target)
    (code : atlas.Code source)
    (hdefect : transport.defect code = 0) :
    atlas.normalizedRead target (transport.map code) =
      atlas.normalizedRead source code := by
  rw [transport.read_map, hdefect, add_zero]

/-- With zero defect, closing is preserved and reflected. -/
theorem closes_iff_of_defect_eq_zero
    (transport : ReadoutTransportWithDefect atlas source target)
    (code : atlas.Code source)
    (hdefect : transport.defect code = 0) :
    atlas.Closes target (transport.map code) ↔
      atlas.Closes source code := by
  unfold ReadoutAtlas.Closes
  rw [transport.read_eq_of_defect_eq_zero code hdefect]

end ReadoutTransportWithDefect

end CPFormal.Logic
