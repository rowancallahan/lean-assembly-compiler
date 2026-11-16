/- Functional Programming in Lean (fp-lean @0abeea5) BLOCKED rows of `Testing/notes/book_survey3.csv` (branch
`booksurvey3`) whose file is in the last third of the sorted example files: `Examples/Props.lean`,
`Examples/Universes.lean`, `douglib/DirTree.lean`.  Each definition is copied verbatim from the file:line of the
survey row (the copy is made by script from the source lines, not retyped).  Only the namespace wrappers, the
`universe` line and the commands are ours; the dependencies a definition names (a structure, a type, an inductive,
a `ConfigIO` abbreviation) are copied verbatim from the same file with their line numbers as well.
Results: see `Testing/notes/BOOK_S3.md`. -/
import Riscv.Frontx.WaCmd
import Riscv.Frontx.SpecHof
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.BookS3
open Proven Proven.Frontx

universe u v
-- Examples/Props.lean
namespace Props
-- Props.lean:95-96 second
def second (xs : List α) (ok : xs.length ≥ 3) : α :=
  xs[ 2 ]
frontx_compile second
-- Props.lean:246 third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
frontx_compile third
-- Props.lean:278 thirdOption
def thirdOption (xs : List α) : Option α := xs[2]?
frontx_compile thirdOption
end Props
-- Examples/Universes.lean
namespace MyList3
-- Universes.lean:159-161 MyList (dependency)
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- Universes.lean:173-174 myListOfList
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
frontx_compile myListOfList
namespace Explicit
-- Universes.lean:197-198 myListOfList (explicit universes)
def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
frontx_compile myListOfList
end Explicit
end MyList3
-- douglib/DirTree.lean
namespace DirTree
-- DirTree.lean:17-19 Config (dependency)
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
frontx_ind_type Config := Config

-- DirTree.lean:24-25 Config.preFile
def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"
frontx_ind Config.preFile on Config

-- DirTree.lean:27-28 Config.preDir
def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "
frontx_ind Config.preDir on Config

-- DirTree.lean:39-40 Config.inDirectory (uses preDir, defined above)
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
frontx_ind Config.inDirectory on Config

-- DirTree.lean:44-47 configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
frontx_compile configFromArgs

-- DirTree.lean:77-81 doList
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action
frontx_hof doList

namespace Readerish
-- DirTree.lean:129-130 ConfigIO (dependency)
def ConfigIO (α : Type) : Type :=
  Config → IO α

-- DirTree.lean:152-153 locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
frontx_compile locally

end Readerish

namespace T
-- DirTree.lean:212-214 ReaderT (dependency)
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
frontx_compile ReaderT

namespace R
-- DirTree.lean:228-229 R.read (uses T.ReaderT)
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
frontx_compile read
end R

end T

end DirTree

end Proven.Frontx.BookS3
