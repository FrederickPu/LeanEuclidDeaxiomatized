import Lean
open Lean Meta Elab Command

/--
A scoped env extension storing ONLY lemma names.
Each scope accumulates names of declarations tagged with the attribute.
-/
abbrev EuclidExtension := SimpleScopedEnvExtension Name (Array Name)

/-- Register an attribute whose application stores lemma names in a scoped extension. -/
def registerEuclidAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO EuclidExtension := do

  -- The extension stores a list of names, and addition just appends a new one.
  let ext : EuclidExtension ← registerSimpleScopedEnvExtension
    { name     := ref
      initial  := #[]
      addEntry := fun acc n => acc.push n
    }

  -- Register the attribute that populates the extension.
  registerBuiltinAttribute
    { ref   := ref
      name  := attrName
      descr := attrDescr
      applicationTime := AttributeApplicationTime.afterCompilation
      add   := fun declName _stx _kind => do
        -- Just store the lemma name
        ext.add declName
      erase := fun _ => pure ()
    }

  return ext

/-- Declare the actual attribute `[euclid]`. -/
initialize euclidExtension : EuclidExtension ←
  registerEuclidAttr `euclid "euclidean geometry inference rules"


/-- Debug command to print stored lemma names. -/
elab "#euclid_post" : command => do
  let names := euclidExtension.getState (← getEnv)
  IO.println s!"Euclid lemmas: {names.reverse}"
  IO.println s!"Euclid lemmas: {names.reverse}"
