(**************************************************************************)
(*  This file is part of dx, a tool to derive C from monadic Gallina.     *)
(*                                                                        *)
(*  Copyright (C) 2021 Université de Lille & CNRS                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(**************************************************************************)

Require Import BinNums List Ascii String Nat.
From elpi Require Import elpi.

Require Import IR.

Open Scope string.
Close Scope nat_scope.

Elpi Command GenerateIntermediateRepresentation.
Elpi Accumulate lp:{{
  %%%% Utils

  % Verbose info
  pred if-verbose-info i:prop.
  :if "VERBOSE_INFO" if-verbose-info P :- !, P.
  if-verbose-info _.

  pred coqlist->list i:term, o:list term.
  coqlist->list {{ nil }} [].
  coqlist->list (app [ {{ @cons }}, _, X, Xs ]) (X :: Ys) :- coqlist->list Xs Ys.

  pred list->coqlist i:term, i:list term, o:term.
  list->coqlist Typ [] {{ @nil lp:Typ }}.
  list->coqlist Typ (X :: Xs) {{ @cons lp:Typ lp:X lp:Ys }} :- list->coqlist Typ Xs Ys.

  pred int->bit i:int, o:term.
  int->bit 0 {{xO}}.
  int->bit 1 {{xI}}.

  pred int->pos i:int, o:term.
  int->pos 1 {{xH}} :- !.
  int->pos N (app [Lower, Highers]) :-
    Bit  is N mod 2, int->bit Bit  Lower,
    Bits is N div 2, int->pos Bits Highers.

  pred int->nat i:int, o:term.
  int->nat 0 {{O}} :- !.
  int->nat N {{S lp:X}} :- M is N - 1, int->nat M X.

  %% Convert Elpi string (used as id) to Coq string
  %% Currently limited to standard identifier characters

  pred chr->ascii i:string, o:term.
  chr->ascii "_" {{ "_"%char }} :- !.
  chr->ascii "A" {{ "A"%char }} :- !.
  chr->ascii "B" {{ "B"%char }} :- !.
  chr->ascii "C" {{ "C"%char }} :- !.
  chr->ascii "D" {{ "D"%char }} :- !.
  chr->ascii "E" {{ "E"%char }} :- !.
  chr->ascii "F" {{ "F"%char }} :- !.
  chr->ascii "G" {{ "G"%char }} :- !.
  chr->ascii "H" {{ "H"%char }} :- !.
  chr->ascii "I" {{ "I"%char }} :- !.
  chr->ascii "J" {{ "J"%char }} :- !.
  chr->ascii "K" {{ "K"%char }} :- !.
  chr->ascii "L" {{ "L"%char }} :- !.
  chr->ascii "M" {{ "M"%char }} :- !.
  chr->ascii "N" {{ "N"%char }} :- !.
  chr->ascii "O" {{ "O"%char }} :- !.
  chr->ascii "P" {{ "P"%char }} :- !.
  chr->ascii "Q" {{ "Q"%char }} :- !.
  chr->ascii "R" {{ "R"%char }} :- !.
  chr->ascii "S" {{ "S"%char }} :- !.
  chr->ascii "T" {{ "T"%char }} :- !.
  chr->ascii "U" {{ "U"%char }} :- !.
  chr->ascii "V" {{ "V"%char }} :- !.
  chr->ascii "W" {{ "W"%char }} :- !.
  chr->ascii "X" {{ "X"%char }} :- !.
  chr->ascii "Y" {{ "Y"%char }} :- !.
  chr->ascii "Z" {{ "Z"%char }} :- !.
  chr->ascii "a" {{ "a"%char }} :- !.
  chr->ascii "b" {{ "b"%char }} :- !.
  chr->ascii "c" {{ "c"%char }} :- !.
  chr->ascii "d" {{ "d"%char }} :- !.
  chr->ascii "e" {{ "e"%char }} :- !.
  chr->ascii "f" {{ "f"%char }} :- !.
  chr->ascii "g" {{ "g"%char }} :- !.
  chr->ascii "h" {{ "h"%char }} :- !.
  chr->ascii "i" {{ "i"%char }} :- !.
  chr->ascii "j" {{ "j"%char }} :- !.
  chr->ascii "k" {{ "k"%char }} :- !.
  chr->ascii "l" {{ "l"%char }} :- !.
  chr->ascii "m" {{ "m"%char }} :- !.
  chr->ascii "n" {{ "n"%char }} :- !.
  chr->ascii "o" {{ "o"%char }} :- !.
  chr->ascii "p" {{ "p"%char }} :- !.
  chr->ascii "q" {{ "q"%char }} :- !.
  chr->ascii "r" {{ "r"%char }} :- !.
  chr->ascii "s" {{ "s"%char }} :- !.
  chr->ascii "t" {{ "t"%char }} :- !.
  chr->ascii "u" {{ "u"%char }} :- !.
  chr->ascii "v" {{ "v"%char }} :- !.
  chr->ascii "w" {{ "w"%char }} :- !.
  chr->ascii "x" {{ "x"%char }} :- !.
  chr->ascii "y" {{ "y"%char }} :- !.
  chr->ascii "z" {{ "z"%char }} :- !.
  chr->ascii "0" {{ "0"%char }} :- !.
  chr->ascii "1" {{ "1"%char }} :- !.
  chr->ascii "2" {{ "2"%char }} :- !.
  chr->ascii "3" {{ "3"%char }} :- !.
  chr->ascii "4" {{ "4"%char }} :- !.
  chr->ascii "5" {{ "5"%char }} :- !.
  chr->ascii "6" {{ "6"%char }} :- !.
  chr->ascii "7" {{ "7"%char }} :- !.
  chr->ascii "8" {{ "8"%char }} :- !.
  chr->ascii "9" {{ "9"%char }} :- !.
  chr->ascii C _ :-
    coq.error "Cannot use character" C "in names", fail.

  pred string->listchr i:string, o:list string.
  string->listchr "" [] :- !.
  string->listchr S (C :: Cs) :-
    L is size S - 1,
    C is substring S 0 1,
    Sm is substring S 1 L,
    string->listchr Sm Cs.

  pred listascii->coqstring i:list term, o:term.
  listascii->coqstring [] {{ EmptyString }}.
  listascii->coqstring (A :: As) {{ String lp:A lp:S }} :- listascii->coqstring As S.

  pred string->coqstring i:string, o:term.
  string->coqstring S CS :-
    string->listchr S Cs,
    std.map Cs chr->ascii As,
    listascii->coqstring As CS.

  pred name->coqstring i:name, o:term.
  name->coqstring N CS :-
    coq.name->id N S,
    string->coqstring S CS.

  pred names->coqliststring i:list name, o:term.
  names->coqliststring Ns LNs :-
    std.map Ns name->coqstring Ss,
    std.rev Ss RSs,
    list->coqlist {{ string }} RSs LNs.

  % Hack full modules into terms, to handle them uniformly...
  type fullModule modpath -> term.

  pred prettyPrint i:term.
  prettyPrint (fullModule MP) :- !, coq.say "full module " MP.
  prettyPrint T :- coq.say { coq.term->string T }.

  pred resolveLoc i:located, o:term.
  resolveLoc (loc-gref G) (global G).
  resolveLoc (loc-modpath MP) (fullModule MP).

  % Hack separator into terms
  type argumentSeparator term.

  pred resolveArg i:argument, o:term.
  resolveArg (trm T) T.
  resolveArg (str "__") argumentSeparator :- !.
  resolveArg (str Name) T :- coq.locate-all Name (Loc :: _), resolveLoc Loc T.

  % Split the argument list at "__"
  pred splitArgs i:list argument, o:list argument, o:list argument.
  splitArgs [str "__"|As] []     As :- !.
  splitArgs [A|As]        [A|Bs] Cs :- splitArgs As Bs Cs.
  splitArgs []            []     [].

  pred resolveConst i:term, o:term.
  resolveConst (global (const C)) B :- !, coq.env.const C (some B) _.
  resolveConst T T.

  type localid int -> term.

  kind primitiveOrGlobal type.
  type pgPrimitive term -> primitiveOrGlobal.
    % ^ The Primitive Record
  type pgGlobal    int -> term -> primitiveOrGlobal.
    % ^ The GlobalId and its CompilableSymbolType

  kind compilableOrMatchable type.
  type compilableType term -> compilableOrMatchable.
  type matchableType  term -> compilableOrMatchable.

  kind configuration type.
  % cfg Monad Bind Return Extern Primitives+Global Matchable
  type cfg term -> term -> term -> term -> coq.gref.map primitiveOrGlobal -> coq.gref.map compilableOrMatchable -> configuration.

  pred resolveType i:compilableOrMatchable, o:term.
  resolveType (compilableType CTyp) CTyp.
  resolveType (matchableType (app [{{MkMatchableType}}, Typ, _, _, _, _])) CTyp :- resolveConst Typ CTyp.

  pred resolveCompilableType i:configuration, i:term, o:term.
  resolveCompilableType (cfg _ _ _ _ _ CMs) (global Typ) CTyp :-
    coq.gref.map.find Typ CMs CMTyp,
    !,
    resolveType CMTyp CTyp.
  resolveCompilableType _ (app [{{MkCompilableType}}, _, _] as CTyp) CTyp :- !.
  resolveCompilableType Cfg (global (const Typ)) CTyp :-
    coq.env.const Typ (some RTyp) _,
    resolveCompilableType Cfg RTyp CTyp.

  pred resolveId i:configuration, i:term, o:term, o:term.
  resolveId (cfg _ _ _ _ PGs _) (global Id) GId STyp :-
    coq.gref.map.find Id PGs (pgGlobal IId STyp),
    !,
    int->pos IId GId.
  resolveId _ (global Id) _ _ :-
    coq.error "Unknown identifier" Id.

  pred matchArgType i:term, o:gref.
  matchArgType (match _ (fun _ (global T) _) _) T.

  pred handleExpression i:configuration, i:term, i:term, o:term.
  :if "trace_handleExpression" handleExpression _ _ X _ :- coq.say "handleExpression:" { coq.term->string X }, fail.
  handleExpression (cfg _ _ _ _ PGs _) _ (global Prim) {{ ePrim lp:CPrim (@nil Expression) }} :-
    coq.gref.map.find Prim PGs (pgPrimitive CPrim), !.
  handleExpression (cfg _ _ _ _ PGs _ as Cfg) _ (app (global Prim :: Args)) {{ ePrim lp:CPrim lp:CArgs }} :-
    coq.gref.map.find Prim PGs (pgPrimitive CPrim),
    CPrim = app [{{MkPrimitive}}, STyp, _, _],
    !,
    handleSubExpressions Cfg STyp Args CArgs.
  handleExpression (cfg _ _ _ _ PGs _) _ (global (const _ as C)) {{ eGlobal lp:CTyp lp:Id (@nil Expression) }} :-
    !,
    coq.gref.map.find C PGs (pgGlobal IId CTyp), % TODO? show debugging message when find fails
    int->pos IId Id.
  % Very strict case for let: it covers only coercions
  handleExpression Cfg _ (let _ Typ Exp x\x) Exp2 :-
    !,
    handleExpression Cfg Typ Exp Exp2.
  handleExpression Cfg Typ (localid I) {{ eLocal lp:CTyp lp:J }} :-
    !,
    resolveCompilableType Cfg Typ CTyp,
    int->pos I J.
  handleExpression _ Typ Trm _ :- coq.say "Fail with expression" Typ Trm, fail.

  pred handleSubExpressions i:configuration, i:term, i:list term, o:term.
  :if "trace_handleSubExpressions" handleSubExpressions _ _ X _ :- coq.say "handleSubExpressions:" { std.map coq.term->string X }, fail.
  handleSubExpressions Cfg STyp Args CArgs :-
    resolveConst STyp (app [{{ MkCompilableSymbolType }}, ArgTyps, _]),
    resolveConst ArgTyps LArgs,
    coqlist->list LArgs ArgTyps2,
    std.map2 ArgTyps2 Args (handleExpression Cfg) EArgs,
    list->coqlist {{ Expression }} EArgs CArgs.

  pred handleMatchBranch i:configuration, i:term, i:int, i:list name, o:term, o:term, o:int, o:list name.
  :if "trace_handleMatchBranch" handleMatchBranch _ X _ _ _ _ _ _ :- coq.say "handleMatchBranch:" { coq.term->string X }, fail.
  handleMatchBranch Cfg (fun X Typ (_\B)) I XNs
    {{@cons MatchedLocalId (@pair TypedLocalId UsedBinding (@pair LocalId CompilableType lp:K lp:CTyp) false) lp:Vs}} Y J ZNs :-
    !, % cut since we know we don’t need the argument
    resolveCompilableType Cfg Typ CTyp,
    int->pos I K,
    L is I + 1,
    handleMatchBranch Cfg B L (X::XNs) Vs Y J ZNs.
  handleMatchBranch Cfg (fun X Typ (x\B x)) I XNs
    {{@cons MatchedLocalId (@pair TypedLocalId UsedBinding (@pair LocalId CompilableType lp:K lp:CTyp) true) lp:Vs}} Y J ZNs :-
    !, % cut, since we have covered all cases of fun
    resolveCompilableType Cfg Typ CTyp,
    int->pos I K,
    L is I + 1,
    handleMatchBranch Cfg (B (localid I)) L (X::XNs) Vs Y J ZNs.
  handleMatchBranch Cfg B I XNs {{ @nil MatchedLocalId }} C J YNs :-
    handleStatement Cfg B I XNs C J YNs.

  pred handleMatchBranches i:configuration, i:list term, i:int, i:list name, o:term, o:int, o:list name.
  handleMatchBranches _ [] I XNs {{ @nil MatchBranchT }} I XNs.
  handleMatchBranches Cfg (B :: Bs) I XNs {{ @cons MatchBranchT (@pair (list MatchedLocalId) Statement lp:Vs lp:C) lp:Xs }} J YNs :-
    handleMatchBranch Cfg B I XNs Vs C L VNs,
    handleMatchBranches Cfg Bs L VNs Xs J YNs.

  pred handleStatement i:configuration, i:term, i:int, i:list name, o:term, o:int, o:list name.
  :if "trace_handleStatement" handleStatement _ X _ _ _ _ _ :- coq.say "handleStatement:" { coq.term->string X }, fail.
  handleStatement (cfg _ _ Ret _ _ _)        (app [Ret, _, {{ tt }}]) I XNs {{ sPure (@None Expression) }}        I XNs :-
    !,
    if-verbose-info (coq.say "INFO: return statement handled").
  handleStatement (cfg _ _ Ret _ _ _ as Cfg) (app [Ret, Typ, V])      I XNs {{ sPure (@Some Expression lp:Exp) }} I XNs :-
    !,
    handleExpression Cfg Typ V Exp,
    if-verbose-info (coq.say "INFO: return statement handled").
  handleStatement (cfg _ Bind _ _ _ _ as Cfg) (app [Bind, _, _, X, fun _ _ (_\B)]) I XNs
                  {{ sBind (@None TypedLocalId) lp:Y lp:C }} J YNs :-
    !,
    handleStatement Cfg X I XNs Y K ZNs,
    handleStatement Cfg B K ZNs C J YNs,
    if-verbose-info (coq.say "INFO: bind statement handled").
  handleStatement (cfg _ Bind _ _ _ _ as Cfg) (app [Bind, Typ, _, X, fun Z _ (x\B x)]) I XNs
                  {{ sBind (@Some TypedLocalId (@pair LocalId CompilableType lp:LI lp:CTyp)) lp:Y lp:C }} J ZNs :-
    !,
    int->pos I LI,
    K is I + 1,
    resolveCompilableType Cfg Typ CTyp,
    handleStatement Cfg X K (Z::XNs) Y L YNs,
    handleStatement Cfg (B (localid I)) L YNs C J ZNs,
    if-verbose-info (coq.say "INFO: bind statement handled").
  handleStatement (cfg _ _ _ _ _ CMs as Cfg) (match Exp (fun _ (global Typ as T) _) Brchs) I XNs {{ sMatch lp:MTyp lp:MExp lp:MBrchs }} J YNs :-
    !,
    coq.gref.map.find Typ CMs (matchableType MTyp),
    handleExpression Cfg T Exp MExp,
    handleMatchBranches Cfg Brchs I XNs MBrchs J YNs,
    if-verbose-info (coq.say "INFO: match statement handled").
  handleStatement Cfg (app (Fun :: Args)) I XNs {{ sApply lp:STyp lp:GId lp:CEArgs }} I XNs :-
    !,
    resolveId Cfg Fun GId STyp,
    handleSubExpressions Cfg STyp Args CEArgs,
    if-verbose-info (coq.say "INFO: call statement handled").
  handleStatement Cfg Fun I XNs {{ sApply lp:STyp lp:GId (@nil Expression) }} I XNs :-
    resolveId Cfg Fun GId STyp,
    !,
    if-verbose-info (coq.say "INFO: call statement handled").
  % Debug handleStatement
  handleStatement _Cfg Trm Int _ _ _ _ :- coq.say "Fail with" Trm Int, fail.

  % TODO? Remove the o:int, if not needed to continue computation
  pred handleFun i:configuration, i:term, i:int, i:list name, o:term, o:int, o:list name.
  :if "trace_handleFun" handleFun _ X _ _ _ _ _ :- coq.say "handleFun:" { coq.term->string X }, fail.
  handleFun Cfg (fun X _ F) I XNs S J YNs :-
    !,
    K is I + 1,
    handleFun Cfg (F (localid I)) K (X::XNs) S J YNs.
  handleFun Cfg Body        I XNs S J YNs :-
    handleStatement Cfg Body I XNs S J YNs,
    if-verbose-info (coq.say "INFO: function handled").

  pred handleFixAndFun i:configuration, i:gref, i:term, i:int, i:list name, o:term, o:int, o:list name, o:term.
  :if "trace_handleFixAndFun" handleFixAndFun _ _ X _ _ _ _ _ _ :- coq.say "handleFixAndFun:" { coq.term->string X }, fail.
  handleFixAndFun Cfg Name (fix _ R _ B) I XNs S J YNs {{ Fix lp:N }} :- !,
    int->nat R N,
    handleFun Cfg (B (global Name)) I XNs S J YNs.
  handleFixAndFun Cfg _ Fun I XNs S J YNs {{ Nofix }} :- handleFun Cfg Fun I XNs S J YNs.

  % Turn a DerivableSymbol into an IRSymbol
  % TODO? Check that the Monad is indeed the one stored in the config
  % (otherwise something really fishy is happening; on the other hand, the
  % output should be verified anyway)
  pred deriveSymbol i:configuration, i:term, o:term.
  :if "trace_deriveSymbol" deriveSymbol _ X _ :- coq.say "deriveSymbol:" { coq.term->string X }, fail.
  deriveSymbol Cfg (app [{{MkDerivableSymbol}}, _Mn, N, M, T, C, {{ true }}])
                   (app [{{MkIRSymbol}},             N, GId, {{ @nil string }}, M, T, {{ None }}, {{ Nofix }}]) :-
      !,
      resolveId Cfg C GId _.
  deriveSymbol Cfg (app [{{MkDerivableSymbol}}, _Mn, N, M, T, (global Name as C), {{ false }}])
                   (app [{{MkIRSymbol}},             N, GId, LNs, M, T, C2, FoNF]) :-
      !,
      resolveConst C C3,
      resolveId Cfg C GId _,
      if (M = {{ true }})
         ( if-verbose-info (coq.say "INFO: Starting derivation of function" Name),
           handleFixAndFun Cfg Name C3 1 [] C4 _ Ns FoNF, C2 = {{ @Some Statement lp:C4 }}, names->coqliststring Ns LNs )
         ( if-verbose-info (coq.say "INFO: Starting derivation of expression" Name),
           handleExpression Cfg T C3 C4, C2 = {{ @Some Expression lp:C4 }}, LNs = {{ @nil string }}, FoNF = {{ Nofix }} ),
      if-verbose-info (coq.say "INFO:" Name "derived").

  pred reGlobal i:gref, o:term.
  reGlobal G (global G).

  pred isConst i:gref.
  isConst (const _).

  pred const->body i:gref, o:term.
  const->body (const C) B :- coq.env.const C (some B) _.

  pred inner-coqType->CompilableSymbolType i:configuration, i:term, o:list term, o:term, o:term.
  inner-coqType->CompilableSymbolType (cfg M _ _ _ _ _) (app [M, {{ unit }}]) [] {{ @None CompilableType }} {{ true }}.
  inner-coqType->CompilableSymbolType (cfg M _ _ _ _ _ as Cfg) (app [M, Typ]) [] {{ @Some CompilableType lp:RTyp }} {{ true }} :-
    resolveCompilableType Cfg Typ RTyp.
  inner-coqType->CompilableSymbolType Cfg Typ [] {{ @Some CompilableType lp:RTyp }} {{ false }} :-
    resolveCompilableType Cfg Typ RTyp.
  inner-coqType->CompilableSymbolType Cfg (prod _ Typ (_\Rest)) (CTyp :: CRest) RTyp M? :-
    resolveCompilableType Cfg Typ CTyp,
    inner-coqType->CompilableSymbolType Cfg Rest CRest RTyp M?.

  % last result: {{ true }} iff the type is monadic
  pred coqType->CompilableSymbolType i:configuration, i:term, o:term, o:term.
  coqType->CompilableSymbolType Cfg Typ {{ MkCompilableSymbolType lp:LTyps lp:RTyp }} M? :-
    inner-coqType->CompilableSymbolType Cfg Typ CTyps RTyp M?,
    list->coqlist {{ CompilableType }} CTyps LTyps.

  pred const->MkDerivable i:configuration, i:gref, o:term.
  const->MkDerivable (cfg M _ _ Extern _ _ as Cfg) (const C as GR)
    {{ MkDerivableSymbol lp:M lp:Name lp:Monadic lp:CSTyp lp:{{global GR}} lp:Extern }} :-
    coq.gref->id GR Id,
    string->coqstring Id Name,
    coq.env.const C _ Typ,
    coqType->CompilableSymbolType Cfg Typ CSTyp Monadic.

  pred oneBuildTermTypeMaps i:configuration,
                            i:int, i:coq.gref.map primitiveOrGlobal, i:coq.gref.map compilableOrMatchable, i: term,
                            o:int, o:coq.gref.map primitiveOrGlobal, o:coq.gref.map compilableOrMatchable, o: option term.
  :if "trace_oneBuildTermTypeMaps" oneBuildTermTypeMaps _ _ _ _ X _ _ _ _ :- coq.say "oneBuildTermTypeMaps:" { coq.term->string X }, fail.
  oneBuildTermTypeMaps _ I PGs CMs (app [{{MkDerivableSymbol}}, _, _, _, _, global Sym, _]) I PGs CMs none :-
    coq.gref.map.mem Sym PGs,
    !,
    coq.warning "dx" "dx.duplicate" "Skip symbol already seen:" { coq.term->string (global Sym) }.
  oneBuildTermTypeMaps _ I PGs CMs (app [{{MkDerivableSymbol}}, _, _, _, STyp, global Sym, _] as Exp) J PGs2 CMs (some Exp) :-
    !,
    coq.gref.map.add Sym (pgGlobal I STyp) PGs PGs2,
    J is I + 1.
  oneBuildTermTypeMaps _ I PGs CMs (app [{{MkPrimitive}}, _, global Sym, _] as Prim) I PGs2 CMs none :-
    !,
    coq.gref.map.add Sym (pgPrimitive Prim) PGs PGs2.
  oneBuildTermTypeMaps _ I PGs CMs (app [{{MkCompilableType}}, global Typ, _] as CTyp) I PGs CMs2 none :-
    !,
    coq.gref.map.add Typ (compilableType CTyp) CMs CMs2.
  oneBuildTermTypeMaps _ I PGs CMs (app [{{MkMatchableType}}, Typ, _, _, _, _] as MTyp) I PGs CMs2 none :-
    !,
    resolveConst Typ (app [{{MkCompilableType}}, (global Typ2), _]),
    coq.gref.map.add Typ2 (matchableType MTyp) CMs CMs2.
  oneBuildTermTypeMaps PreCfg I PGs CMs (global (const C)) J PGs2 CMs2 Exp :-
    coq.env.const C (some B) _,
    oneBuildTermTypeMaps PreCfg I PGs CMs B J PGs2 CMs2 Exp,
    !.
  oneBuildTermTypeMaps (cfg M B R E _ _ as PreCfg) I PGs CMs (global GR) J PGs2 CMs2 Exp :-
    const->MkDerivable (cfg M B R E PGs CMs) GR ExpSym,
    !,
    oneBuildTermTypeMaps PreCfg I PGs CMs ExpSym J PGs2 CMs2 Exp,
    !.

  % index on list?
  % buildTermTypeMaps firstFreshGlobalId startPrimGlobMap
  pred buildTermTypeMaps i:configuration,
                         i:int, i:coq.gref.map primitiveOrGlobal, i:coq.gref.map compilableOrMatchable, i: list term,
                         o:int, o:coq.gref.map primitiveOrGlobal, o:coq.gref.map compilableOrMatchable, o: list term.
  buildTermTypeMaps _ I PGs CMs [] I PGs CMs [] :- !.
  buildTermTypeMaps (cfg M B R _ PGs CMs) I PG1s CM1s (argumentSeparator :: Ts) J PG2s CM2s Exps :-
    !,
    buildTermTypeMaps (cfg M B R {{ false }} PGs CMs) I PG1s CM1s Ts J PG2s CM2s Exps.
  buildTermTypeMaps PreCfg I PGs CMs (fullModule MP :: Ts) J PGs2 CMs2 Exps :-
    !,
    coq.env.module MP GRs,
    std.filter GRs isConst GRs2,
    std.map GRs2 reGlobal GRs3,
    buildTermTypeMaps PreCfg I PGs CMs GRs3 K PGs3 CMs3 Exps3,
    !,
    buildTermTypeMaps PreCfg K PGs3 CMs3 Ts J PGs2 CMs2 Exps2,
    !,
    std.append Exps3 Exps2 Exps.
  buildTermTypeMaps PreCfg I PGs CMs (T :: Ts) J PGs2 CMs2 Exps :-
    oneBuildTermTypeMaps PreCfg I PGs CMs T K PGs3 CMs3 Exp,
    !,
    buildTermTypeMaps PreCfg K PGs3 CMs3 Ts J PGs2 CMs2 Exps2,
    !,
    if (Exp = some Exp2) (Exps = Exp2 :: Exps2) (Exps = Exps2).

  %% Debugging
  buildTermTypeMaps PreCfg I PGs CMs (X :: Ts) J PGs2 CMs2 Exps :-
    coq.warning "dx" "dx.inconvertible" "Cannot convert, skipping:" { coq.term->string X },
    buildTermTypeMaps PreCfg I PGs CMs Ts J PGs2 CMs2 Exps.

  pred buildConfigAndFilterArgs i:list argument, o:configuration, o:list term.
  % TODO? Maybe we could tolerate when Monad, Bind and Return are not given as string
  buildConfigAndFilterArgs Args (cfg Monad Bind Return {{ false }} PGs CMs) Derivables :-
    std.map Args resolveArg [Monad, Bind, Return | PGCMs],
    PreCfg = cfg Monad Bind Return {{ true }} {coq.gref.map.empty} {coq.gref.map.empty},
    buildTermTypeMaps PreCfg 1 {coq.gref.map.empty} {coq.gref.map.empty} PGCMs _ PGs CMs Derivables.

  main (str Res :: Args) :-
    buildConfigAndFilterArgs Args Config Derivables,
    if-verbose-info (coq.say "INFO: Config built"),
    std.map Derivables (deriveSymbol Config) IRSyms,
    if-verbose-info (coq.say "INFO: Symbols derived"),
    list->coqlist {{ IRSymbol }} IRSyms CoqIRSyms,
    std.assert-ok! (coq.typecheck CoqIRSyms Typ) "Error typechecking IR symbols",
    if-verbose-info (coq.say "INFO: Symbols typechecked"),
    coq.env.add-const Res CoqIRSyms Typ _ _.
}}.
Elpi Typecheck.
Elpi Export GenerateIntermediateRepresentation.
