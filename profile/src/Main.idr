module Main

import Data.List
import Data.SnocList
import Data.String
import Package
import PackageLexer
import Parser.Lexer.Package
import Profile
import Text.ILex.Util

small, large : String

veryLarge : String
veryLarge = fastConcat $ replicate 100 large

bench : Benchmark Void
bench = Group "lex-ipkg"
  [ Group "small"
      [ Single "ilex"       (basic lexTok small)
      , Single "idris-api"  (basic lex small)
      ]
  , Group "large"
      [ Single "ilex"       (basic lexTok large)
      , Single "idris-api"  (basic lex large)
      ]
  , Group "very-large"
      [ Single "ilex"       (basic lexTok veryLarge)
      , Single "idris-api"  (basic lex veryLarge)
      ]
  ]

main : IO ()
main = runDefault (const True) Table show bench

small =
  """
  package ilex
  version = 0.1.0
  authors = "stefan-hoeck"
  brief   = "Generating fast Lexers from an Idris2 DSL"
  langversion >= 0.7
  depends = elab-util
          , elab-pretty

  sourcedir = "src"

  modules = Text.ILex
          , Text.ILex.Args
          , Text.ILex.Codegen
          , Text.ILex.DFA
          , Text.ILex.Expr
          , Text.ILex.Set
          , Text.ILex.Util
          , Text.ILex.Val
  """

large =
  """
  package idris2
  version = 0.7.0

  modules =
      Algebra,
      Algebra.Preorder,
      Algebra.Semiring,
      Algebra.SizeChange,
      Algebra.ZeroOneOmega,

      Compiler.ANF,
      Compiler.CaseOpts,
      Compiler.Common,
      Compiler.CompileExpr,
      Compiler.Generated,
      Compiler.Inline,
      Compiler.LambdaLift,
      Compiler.NoMangle,
      Compiler.Opts.CSE,
      Compiler.Separate,
      Compiler.VMCode,

      Compiler.Opts.ConstantFold,
      Compiler.Opts.Identity,
      Compiler.Opts.InlineHeuristics,
      Compiler.Opts.ToplevelConstants,

      Compiler.ES.Ast,
      Compiler.ES.Codegen,
      Compiler.ES.Doc,
      Compiler.ES.Javascript,
      Compiler.ES.Node,
      Compiler.ES.State,
      Compiler.ES.TailRec,
      Compiler.ES.ToAst,

      Compiler.Interpreter.VMCode,

      Compiler.RefC,
      Compiler.RefC.CC,
      Compiler.RefC.RefC,

      Compiler.Scheme.Chez,
      Compiler.Scheme.ChezSep,
      Compiler.Scheme.Racket,
      Compiler.Scheme.Gambit,
      Compiler.Scheme.Common,

      Core.AutoSearch,
      Core.Binary,
      Core.Binary.Prims,
      Core.Case.CaseBuilder,
      Core.Case.CaseTree,
      Core.Case.CaseTree.Pretty,
      Core.Case.Util,
      Core.CompileExpr,
      Core.CompileExpr.Pretty,
      Core.Context,
      Core.Context.Context,
      Core.Context.Data,
      Core.Context.Log,
      Core.Context.Pretty,
      Core.Context.TTC,
      Core.Core,
      Core.Coverage,
      Core.Directory,
      Core.Env,
      Core.FC,
      Core.GetType,
      Core.Hash,
      Core.InitPrimitives,
      Core.LinearCheck,
      Core.Metadata,
      Core.Name,
      Core.Name.Namespace,
      Core.Name.Scoped,
      Core.Normalise,
      Core.Normalise.Convert,
      Core.Normalise.Eval,
      Core.Normalise.Quote,
      Core.Options,
      Core.Options.Log,
      Core.Ord,
      Core.Primitives,
      Core.Reflect,
      Core.SchemeEval,
      Core.Termination.CallGraph,
      Core.Termination.SizeChange,
      Core.Termination.Positivity,
      Core.Termination.References,
      Core.Termination,
      Core.Transform,
      Core.TT,
      Core.TT.Binder,
      Core.TT.Primitive,
      Core.TT.Subst,
      Core.TT.Term,
      Core.TT.Term.Subst,
      Core.TT.Traversals,
      Core.TT.Var,
      Core.TT.Views,
      Core.TTC,
      Core.Unify,
      Core.UnifyState,
      Core.Value,

      Core.SchemeEval.Builtins,
      Core.SchemeEval.Compile,
      Core.SchemeEval.Evaluate,
      Core.SchemeEval.Quote,
      Core.SchemeEval.ToScheme,

      IdrisPaths,

      Idris.CommandLine,
      Idris.Desugar,
      Idris.Desugar.Mutual,
      Idris.Env,
      Idris.Doc.Annotations,
      Idris.Doc.Brackets,
      Idris.Doc.Display,
      Idris.Doc.Keywords,
      Idris.Doc.HTML,
      Idris.Doc.String,
      Idris.Driver,
      Idris.Error,
      Idris.ModTree,

      Idris.Package,
      Idris.Package.Init,
      Idris.Package.ToJson,
      Idris.Package.Types,

      Idris.Parser,
      Idris.Parser.Let,
      Idris.Pretty,
      Idris.Pretty.Annotations,
      Idris.Pretty.Render,
      Idris.ProcessIdr,
      Idris.REPL,
      Idris.Resugar,
      Idris.SetOptions,
      Idris.Syntax,
      Idris.Syntax.Builtin,
      Idris.Syntax.Pragmas,
      Idris.Syntax.TTC,
      Idris.Syntax.Traversals,
      Idris.Syntax.Views,
      Idris.Version,

      Idris.Elab.Implementation,
      Idris.Elab.Interface,

      Idris.IDEMode.CaseSplit,
      Idris.IDEMode.Commands,
      Idris.IDEMode.Holes,
      Idris.IDEMode.MakeClause,
      Idris.IDEMode.Parser,
      Idris.IDEMode.Pretty,
      Idris.IDEMode.REPL,
      Idris.IDEMode.SyntaxHighlight,
      Idris.IDEMode.TokenLine,

      Idris.REPL.Common,
      Idris.REPL.Opts,
      Idris.REPL.FuzzySearch,

      Libraries.Control.ANSI,
      Libraries.Control.ANSI.CSI,
      Libraries.Control.ANSI.SGR,
      Libraries.Control.Delayed,

      Libraries.Data.ANameMap,
      Libraries.Data.DList,
      Libraries.Data.Erased,
      Libraries.Data.Fin,
      Libraries.Data.Graph,
      Libraries.Data.IMaybe,
      Libraries.Data.IntMap,
      Libraries.Data.IOArray,
      Libraries.Data.IOMatrix,
      Libraries.Data.List.Extra,
      Libraries.Data.List.HasLength,
      Libraries.Data.List.Lazy,
      Libraries.Data.List.LengthMatch,
      Libraries.Data.List.Quantifiers.Extra,
      Libraries.Data.List.SizeOf,
      Libraries.Data.List1,
      Libraries.Data.NameMap,
      Libraries.Data.NameMap.Traversable,
      Libraries.Data.Ordering.Extra,
      Libraries.Data.PosMap,
      Libraries.Data.SnocList.HasLength,
      Libraries.Data.SnocList.LengthMatch,
      Libraries.Data.SnocList.SizeOf,
      Libraries.Data.Span,
      Libraries.Data.SortedMap,
      Libraries.Data.SortedSet,
      Libraries.Data.SparseMatrix,
      Libraries.Data.String.Builder,
      Libraries.Data.String.Extra,
      Libraries.Data.String.Iterator,
      Libraries.Data.StringMap,
      Libraries.Data.StringTrie,
      Libraries.Data.Tap,
      Libraries.Data.UserNameMap,
      Libraries.Data.Version,
      Libraries.Data.WithDefault,

      Libraries.System.Directory.Tree,

      Libraries.Text.Bounded,
      Libraries.Text.Distance.Levenshtein,
      Libraries.Text.Lexer,
      Libraries.Text.Lexer.Core,
      Libraries.Text.Lexer.Tokenizer,
      Libraries.Text.Literate,
      Libraries.Text.Parser,
      Libraries.Text.Parser.Core,
      Libraries.Text.PrettyPrint.Prettyprinter,
      Libraries.Text.PrettyPrint.Prettyprinter.Doc,
      Libraries.Text.PrettyPrint.Prettyprinter.Render.HTML,
      Libraries.Text.PrettyPrint.Prettyprinter.Render.String,
      Libraries.Text.PrettyPrint.Prettyprinter.Render.Terminal,
      Libraries.Text.PrettyPrint.Prettyprinter.SimpleDocTree,
      Libraries.Text.PrettyPrint.Prettyprinter.Symbols,
      Libraries.Text.PrettyPrint.Prettyprinter.Util,
      Libraries.Text.Quantity,
      Libraries.Text.Token,

      Libraries.Utils.Binary,
      Libraries.Utils.Octal,
      Libraries.Utils.Path,
      Libraries.Utils.Scheme,
      Libraries.Utils.Shunting,
      Libraries.Utils.String,

      Parser.Package,
      Parser.Source,
      Parser.Support,
      Parser.Support.Escaping,
      Parser.Unlit,

      Parser.Lexer.Common,
      Parser.Lexer.Package,
      Parser.Lexer.Source,

      Parser.Rule.Package,
      Parser.Rule.Source,

      Protocol.IDE,
      Protocol.IDE.Command,
      Protocol.IDE.Decoration,
      Protocol.IDE.FileContext,
      Protocol.IDE.Formatting,
      Protocol.IDE.Holes,
      Protocol.IDE.Result,
      Protocol.IDE.Highlight,
      Protocol.Hex,
      Protocol.SExp,
      Protocol.SExp.Parser,

      TTImp.BindImplicits,
      TTImp.Elab,
      TTImp.Impossible,
      TTImp.Parser,
      TTImp.PartialEval,
      TTImp.ProcessBuiltin,
      TTImp.ProcessData,
      TTImp.ProcessDecls,
      TTImp.ProcessDecls.Totality,
      TTImp.ProcessDef,
      TTImp.ProcessFnOpt,
      TTImp.ProcessParams,
      TTImp.ProcessRecord,
      TTImp.ProcessRunElab,
      TTImp.ProcessTransform,
      TTImp.ProcessType,
      TTImp.Reflect,
      TTImp.TTImp,
      TTImp.TTImp.Functor,
      TTImp.TTImp.Traversals,
      TTImp.TTImp.TTC,
      TTImp.Unelab,
      TTImp.Utils,
      TTImp.WithClause,

      TTImp.Elab.Ambiguity,
      TTImp.Elab.App,
      TTImp.Elab.As,
      TTImp.Elab.Binders,
      TTImp.Elab.Case,
      TTImp.Elab.Check,
      TTImp.Elab.Delayed,
      TTImp.Elab.Dot,
      TTImp.Elab.Hole,
      TTImp.Elab.ImplicitBind,
      TTImp.Elab.Lazy,
      TTImp.Elab.Local,
      TTImp.Elab.Prim,
      TTImp.Elab.Quote,
      TTImp.Elab.Record,
      TTImp.Elab.Rewrite,
      TTImp.Elab.RunElab,
      TTImp.Elab.Term,
      TTImp.Elab.Utils,

      TTImp.Interactive.CaseSplit,
      TTImp.Interactive.Completion,
      TTImp.Interactive.ExprSearch,
      TTImp.Interactive.GenerateDef,
      TTImp.Interactive.Intro,
      TTImp.Interactive.MakeLemma,

      Yaffle.Main,
      Yaffle.REPL

  depends = network

  sourcedir = "src"
  """