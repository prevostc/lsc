import Lean.LabelAttribute

initialize lscExternalExt : Lean.LabelExtension ←
  Lean.registerLabelAttr `lsc.external "LSC external function marker" `lscExternalExt
syntax (name := Parser.Attr.lsc.external) "lsc.external" : attr

initialize lscErrorExt : Lean.LabelExtension ←
  Lean.registerLabelAttr `lsc.error "LSC error type marker" `lscErrorExt
syntax (name := Parser.Attr.lsc.error) "lsc.error" : attr

/-- Marks a `Field` constant as publicly exposed in the contract ABI.
    The codegen walker uses this to discover entrypoints. -/
initialize lscPublicExt : Lean.LabelExtension ←
  Lean.registerLabelAttr `lsc.public "LSC public ABI field" `lscPublicExt
syntax (name := Parser.Attr.lsc.public) "lsc.public" : attr
