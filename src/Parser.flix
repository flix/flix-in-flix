pub enum Token with ToString {
    case Name(String)
    case IntLit(Int32)
    case CharLit(Char)
    case KwTrait
    case KwInstance
    case KwEnum
    case KwDef
    case KwType
    case KwForall
    case KwIf
    case KwThen
    case KwElse
    case KwDo
    case KwRun
    case KwWithout
    case KwTrue
    case KwFalse
    case KwKindType
    case KwKindEff
    case LParen
    case RParen
    case LBracket
    case RBracket
    case LBrace
    case RBrace
    case Colon
    case Comma
    case Dot
    case Equals
    case Tilde
    case Plus
    case Amp
    case Caret
    case Backslash
    case Arrow
    case FatArrow
    case SuperArrow
}

pub enum SType {
    case Var(Id)
    case EffVar(Id)
    case Con(Id)
    case App(SType, SType)
    case Assoc(Id, SType)
    case Fun(SType, SType, SType)
    case EffEmpty
    case EffConst(Id)
    case EffUnion(SType, SType)
    case EffIntersect(SType, SType)
    case EffXor(SType, SType)
    case EffCompl(SType)
}

pub enum SConstr {
    case Class(Id, SType)
    case Eq(SType, SType)
}

pub enum SExpr {
    case Var(Id)
    case LitInt32
    case LitBool(Bool)
    case LitChar
    case LitUnit
    case Ap(SExpr, SExpr)
    case Lam(Id, SExpr)
    case IfElse(SExpr, SExpr, SExpr)
    case Do(Id)
    case RunWithout(SExpr, Id)
}

pub type alias SBinder = (Id, Kind)
pub type alias SAssocEq = (Id, Kind, SType)
pub type alias ParsedProgram = (ConstrEnv, List[TopLevelDecl])
type alias SurfaceState = (
    Map[Id, Kind], // type constructor kinds
    Map[Id, Kind], // trait argument kinds
    Map[Id, Kind], // associated member result kinds
    ConstrEnv,
    List[TopLevelDecl]
)
type alias ParseResult[a] = Result[String, (a, List[Token])]

mod SurfaceState {
    pub def tycons(st: SurfaceState): Map[Id, Kind] = let (x, _, _, _, _) = st; x
    pub def traits(st: SurfaceState): Map[Id, Kind] = let (_, x, _, _, _) = st; x
    pub def assocs(st: SurfaceState): Map[Id, Kind] = let (_, _, x, _, _) = st; x
    pub def env(st: SurfaceState): ConstrEnv = let (_, _, _, x, _) = st; x
    pub def decls(st: SurfaceState): List[TopLevelDecl] = let (_, _, _, _, x) = st; x

    pub def withTycons(tycons: Map[Id, Kind], st: SurfaceState): SurfaceState = {
        let (_, traits, assocs, env, decls) = st;
        (tycons, traits, assocs, env, decls)
    }

    pub def withTraits(traits: Map[Id, Kind], st: SurfaceState): SurfaceState = {
        let (tycons, _, assocs, env, decls) = st;
        (tycons, traits, assocs, env, decls)
    }

    pub def withAssocs(assocs: Map[Id, Kind], st: SurfaceState): SurfaceState = {
        let (tycons, traits, _, env, decls) = st;
        (tycons, traits, assocs, env, decls)
    }

    pub def withEnv(env: ConstrEnv, st: SurfaceState): SurfaceState = {
        let (tycons, traits, assocs, _, decls) = st;
        (tycons, traits, assocs, env, decls)
    }

    pub def withDecls(decls: List[TopLevelDecl], st: SurfaceState): SurfaceState = {
        let (tycons, traits, assocs, env, _) = st;
        (tycons, traits, assocs, env, decls)
    }
}

mod Parser {
    pub def parseProgram(src: String): Result[String, ParsedProgram] =
        Result.flatMap(
            ts -> parseItems(initialState(), ts),
            lex(src)
        )

    pub def parseAndTypeCheck(src: String): Result[String, List[Check]] \ Fresh =
        Result.map(
            p -> {
                let (env, decls) = p;
                typeCheckProgram(env, decls)
            },
            parseProgram(src)
        )

    def initialState(): SurfaceState = (
        builtInTycons(),
        Map.empty(),
        Map.empty(),
        ConstrEnv.empty(),
        Nil
    )

    def builtInTycons(): Map[Id, Kind] =
        Map.empty()
            |> Map.insert("Unit", Kind.Star)
            |> Map.insert("Int32", Kind.Star)
            |> Map.insert("Char", Kind.Star)
            |> Map.insert("Bool", Kind.Star)
            |> Map.insert("List", Kind.KFun(Kind.Star, Kind.Star))

    def lex(src: String): Result[String, List[Token]] =
        lexLoop(src, 0, Nil)

    def lexLoop(src: String, i: Int32, acc: List[Token]): Result[String, List[Token]] =
        if (i >= String.length(src)) Ok(List.reverse(acc))
        else {
            let c = String.charAt(i, src);
            if (Char.isWhitespace(c)) lexLoop(src, i + 1, acc)
            else if (c == '/' and hasNext(src, i) and String.charAt(i + 1, src) == '/')
                lexLoop(src, skipComment(src, i + 2), acc)
            else if (c == '-' and hasNext(src, i) and String.charAt(i + 1, src) == '>')
                lexLoop(src, i + 2, Token.Arrow :: acc)
            else if (c == '=' and hasNext(src, i) and String.charAt(i + 1, src) == '>')
                lexLoop(src, i + 2, Token.FatArrow :: acc)
            else if (c == '<' and hasNext(src, i) and String.charAt(i + 1, src) == ':')
                lexLoop(src, i + 2, Token.SuperArrow :: acc)
            else if (Char.isLetter(c) or c == '_')
                let j = scanName(src, i + 1);
                let name = String.slice(start = i, end = j, src);
                lexLoop(src, j, classifyName(name) :: acc)
            else if (Char.isDigit(c))
                let j = scanDigits(src, i + 1);
                let digits = String.slice(start = i, end = j, src);
                match Int32.fromString(digits) {
                    case Some(n) => lexLoop(src, j, Token.IntLit(n) :: acc)
                    case None => Err("Invalid integer literal: ${digits}")
                }
            else match c {
                case '\'' => lexChar(src, i, acc)
                case '(' => lexLoop(src, i + 1, Token.LParen :: acc)
                case ')' => lexLoop(src, i + 1, Token.RParen :: acc)
                case '[' => lexLoop(src, i + 1, Token.LBracket :: acc)
                case ']' => lexLoop(src, i + 1, Token.RBracket :: acc)
                case '{' => lexLoop(src, i + 1, Token.LBrace :: acc)
                case '}' => lexLoop(src, i + 1, Token.RBrace :: acc)
                case ':' => lexLoop(src, i + 1, Token.Colon :: acc)
                case ',' => lexLoop(src, i + 1, Token.Comma :: acc)
                case '.' => lexLoop(src, i + 1, Token.Dot :: acc)
                case '=' => lexLoop(src, i + 1, Token.Equals :: acc)
                case '~' => lexLoop(src, i + 1, Token.Tilde :: acc)
                case '+' => lexLoop(src, i + 1, Token.Plus :: acc)
                case '&' => lexLoop(src, i + 1, Token.Amp :: acc)
                case '^' => lexLoop(src, i + 1, Token.Caret :: acc)
                case '\\' => lexLoop(src, i + 1, Token.Backslash :: acc)
                case _ => Err("Unexpected character `${c}` at offset ${i}.")
            }
        }

    def hasNext(src: String, i: Int32): Bool = i + 1 < String.length(src)

    def skipComment(src: String, i: Int32): Int32 =
        if (i >= String.length(src)) i
        else if (String.charAt(i, src) == '\n') i + 1
        else skipComment(src, i + 1)

    def scanName(src: String, i: Int32): Int32 =
        if (i >= String.length(src)) i
        else {
            let c = String.charAt(i, src);
            if (Char.isLetterOrDigit(c) or c == '_') scanName(src, i + 1) else i
        }

    def scanDigits(src: String, i: Int32): Int32 =
        if (i >= String.length(src)) i
        else if (Char.isDigit(String.charAt(i, src))) scanDigits(src, i + 1) else i

    def classifyName(name: String): Token = match name {
        case "trait" => Token.KwTrait
        case "instance" => Token.KwInstance
        case "enum" => Token.KwEnum
        case "def" => Token.KwDef
        case "type" => Token.KwType
        case "forall" => Token.KwForall
        case "if" => Token.KwIf
        case "then" => Token.KwThen
        case "else" => Token.KwElse
        case "do" => Token.KwDo
        case "run" => Token.KwRun
        case "without" => Token.KwWithout
        case "true" => Token.KwTrue
        case "false" => Token.KwFalse
        case "Type" => Token.KwKindType
        case "Eff" => Token.KwKindEff
        case _ => Token.Name(name)
    }

    def lexChar(src: String, i: Int32, acc: List[Token]): Result[String, List[Token]] =
        if (i + 2 >= String.length(src)) Err("Unterminated character literal.")
        else {
            let c = String.charAt(i + 1, src);
            if (c == '\\') {
                if (i + 3 >= String.length(src)) Err("Unterminated character literal.")
                else {
                    let esc = String.charAt(i + 2, src);
                    let q = String.charAt(i + 3, src);
                    if (q != '\'') Err("Expected closing quote in character literal.")
                    else lexLoop(src, i + 4, Token.CharLit(unescapeChar(esc)) :: acc)
                }
            } else {
                let q = String.charAt(i + 2, src);
                if (q != '\'') Err("Expected closing quote in character literal.")
                else lexLoop(src, i + 3, Token.CharLit(c) :: acc)
            }
        }

    def unescapeChar(c: Char): Char = match c {
        case 'n' => '\n'
        case 'r' => '\r'
        case 't' => '\t'
        case '\\' => '\\'
        case '\'' => '\''
        case _ => c
    }

    def parseItems(st: SurfaceState, ts: List[Token]): Result[String, ParsedProgram] = match ts {
        case Nil => Ok((SurfaceState.env(st), List.reverse(SurfaceState.decls(st))))
        case Token.KwTrait :: _ => Result.flatMap(
            pair -> {
                let (st1, rest) = pair;
                parseItems(st1, rest)
            },
            parseTraitDecl(st, ts)
        )
        case Token.KwEnum :: _ => Result.flatMap(
            pair -> {
                let (st1, rest) = pair;
                parseItems(st1, rest)
            },
            parseEnumDecl(st, ts)
        )
        case Token.KwInstance :: _ => Result.flatMap(
            pair -> {
                let (st1, rest) = pair;
                parseItems(st1, rest)
            },
            parseInstanceDecl(st, ts)
        )
        case Token.KwDef :: _ => Result.flatMap(
            pair -> {
                let (st1, rest) = pair;
                parseItems(st1, rest)
            },
            parseTopDecl(st, ts)
        )
        case t :: _ => Err("Unexpected token at top-level: ${t}")
    }

    def parseTraitDecl(st: SurfaceState, ts: List[Token]): Result[String, (SurfaceState, List[Token])] = match ts {
        case Token.KwTrait :: Token.Name(name) :: Token.LBracket :: rest =>
            Result.flatMap(
                binderRes -> {
                    let (binder, rest1) = binderRes;
                    match rest1 {
                        case Token.RBracket :: rest2 =>
                            let traitKinds = Map.insert(name, snd(binder), SurfaceState.traits(st));
                            let env0 = ConstrEnv.addClass(name, SurfaceState.env(st));
                            parseOptionalSuper(st, rest2)
                                |> Result.flatMap(pair -> {
                                    let (superOpt, rest3) = pair;
                                    let env1 = match superOpt {
                                        case None => env0
                                        case Some(sup) => ConstrEnv.addSuper(name, sup, env0)
                                    };
                                    parseTraitBody(rest3)
                                        |> Result.map(bodyRes -> {
                                            let (assocDecls, rest4) = bodyRes;
                                            let assocKinds = List.foldLeft(
                                                (acc, decl) -> {
                                                    let (assocName, kind) = decl;
                                                    Map.insert(assocName, kind, acc)
                                                },
                                                SurfaceState.assocs(st),
                                                assocDecls
                                            );
                                            (
                                                st
                                                    |> SurfaceState.withTraits(traitKinds)
                                                    |> SurfaceState.withAssocs(assocKinds)
                                                    |> SurfaceState.withEnv(env1),
                                                rest4
                                            )
                                        })
                                })
                        case _ => Err("Expected `]` after trait binder.")
                    }
                },
                parseBinder(rest)
            )
        case _ => Err("Malformed trait declaration.")
    }

    def parseOptionalSuper(st: SurfaceState, ts: List[Token]): Result[String, (Option[Id], List[Token])] = match ts {
        case Token.SuperArrow :: rest =>
            Result.map(
                pair -> {
                    let ((name, _), rest1) = pair;
                    (Some(name), rest1)
                },
                parseTraitHead(st, rest)
            )
        case _ => Ok((None, ts))
    }

    def parseTraitBody(ts: List[Token]): Result[String, (List[(Id, Kind)], List[Token])] = match ts {
        case Token.LBrace :: rest => parseTraitDecls(rest, Nil)
        case _ => Ok((Nil, ts))
    }

    def parseTraitDecls(ts: List[Token], acc: List[(Id, Kind)]): Result[String, (List[(Id, Kind)], List[Token])] = match ts {
        case Token.RBrace :: rest => Ok((List.reverse(acc), rest))
        case Token.KwType :: Token.Name(name) :: rest =>
            Result.flatMap(
                pair -> {
                    let (kind, rest1) = pair;
                    parseTraitDecls(rest1, (name, kind) :: acc)
                },
                parseOptionalResultKind(rest, Kind.Star)
            )
        case _ => Err("Expected associated member declaration or `}`.")
    }

    def parseEnumDecl(st: SurfaceState, ts: List[Token]): Result[String, (SurfaceState, List[Token])] = match ts {
        case Token.KwEnum :: Token.Name(name) :: Token.LBracket :: rest =>
            Result.flatMap(
                bindersRes -> {
                    let (binders, rest1) = bindersRes;
                    match rest1 {
                        case Token.RBracket :: rest2 =>
                            let kind = enumKind(binders);
                            let tycons = Map.insert(name, kind, SurfaceState.tycons(st));
                            Ok((SurfaceState.withTycons(tycons, st), rest2))
                        case _ => Err("Expected `]` after enum binders.")
                    }
                },
                parseBinderList(rest)
            )
        case _ => Err("Malformed enum declaration.")
    }

    def parseInstanceDecl(st: SurfaceState, ts: List[Token]): Result[String, (SurfaceState, List[Token])] = match ts {
        case Token.KwInstance :: rest =>
            Result.flatMap(
                pair -> {
                    let ((ctxs, head), rest1) = pair;
                    let (headName, headArg) = head;
                    let inst = Inst.Inst(Qual.Qual(
                        List.map(lowerConstr(st, Map.empty()), ctxs),
                        lowerClassHead(st, head)
                    ));
                    let env0 = ConstrEnv.addInst(headName, inst, SurfaceState.env(st));
                    Result.flatMap(
                        bodyRes -> {
                            let (assocEqs, rest2) = bodyRes;
                            let env1 = List.foldLeft(
                                (acc, eq) -> {
                                    let (assocName, kind, rhs) = eq;
                                    let lhs = Type.Assoc(Tyassoc.Tyassoc(
                                        assocName,
                                        lowerType(st, Map.empty(), headArg),
                                        kind
                                    ));
                                    let rhsTy = lowerType(st, Map.empty(), rhs);
                                    ConstrEnv.addAssocEq(assocName, (lhs, rhsTy), acc)
                                },
                                env0,
                                assocEqs
                            );
                            Ok((SurfaceState.withEnv(env1, st), rest2))
                        },
                        parseOptionalInstanceBody(st, rest1)
                    )
                },
                parseInstanceHeadAndContext(st, rest)
            )
        case _ => Err("Malformed instance declaration.")
    }

    def parseOptionalInstanceBody(st: SurfaceState, ts: List[Token]): Result[String, (List[SAssocEq], List[Token])] = match ts {
        case Token.LBrace :: rest => parseAssocEqs(st, rest, Nil)
        case _ => Ok((Nil, ts))
    }

    def parseAssocEqs(st: SurfaceState, ts: List[Token], acc: List[SAssocEq]): Result[String, (List[SAssocEq], List[Token])] = match ts {
        case Token.RBrace :: rest => Ok((List.reverse(acc), rest))
        case Token.KwType :: Token.Name(name) :: rest =>
            let declaredKind = Option.getWithDefault(Kind.Star, Map.get(name, SurfaceState.assocs(st)));
            parseOptionalResultKind(rest, declaredKind)
                |> Result.flatMap(pair -> {
                    let (kind, rest1) = pair;
                    match rest1 {
                        case Token.Equals :: rest2 =>
                            parseAssocValue(st, kind, rest2)
                                |> Result.flatMap(rhsRes -> {
                                    let (rhs, rest3) = rhsRes;
                                    parseAssocEqs(st, rest3, (name, kind, rhs) :: acc)
                                })
                        case _ => Err("Expected `=` in associated equality.")
                    }
                })
        case _ => Err("Expected associated equality or `}`.")
    }

    def parseAssocValue(st: SurfaceState, kind: Kind, ts: List[Token]): ParseResult[SType] =
        if (kind == Kind.Eff) parseEffect(st, ts) else parseType(st, ts)

    def parseTopDecl(st: SurfaceState, ts: List[Token]): Result[String, (SurfaceState, List[Token])] = match ts {
        case Token.KwDef :: Token.Name(name) :: Token.Colon :: rest =>
            Result.flatMap(
                schemeRes -> {
                    let ((schemeBinders, schemeCtx, schemeTy), rest1) = schemeRes;
                    match rest1 {
                        case Token.Equals :: rest2 =>
                            Result.flatMap(
                                exprRes -> {
                                    let (expr, rest3) = exprRes;
                                    let decl = (
                                        name,
                                        lowerScheme(st, schemeBinders, schemeCtx, schemeTy),
                                        lowerExpr(expr)
                                    );
                                    Ok((
                                        SurfaceState.withDecls(decl :: SurfaceState.decls(st), st),
                                        rest3
                                    ))
                                },
                                parseExpr(rest2)
                            )
                        case _ => Err("Expected `=` in top-level declaration.")
                    }
                },
                parseScheme(st, rest)
            )
        case _ => Err("Malformed top-level declaration.")
    }

    def parseScheme(st: SurfaceState, ts: List[Token]): Result[String, ((List[SBinder], List[SConstr], SType), List[Token])] = 
        Result.flatMap(
            bindersRes -> {
                let (binders, rest1) = bindersRes;
                let vars = binderMap(binders);
                match tryConstraintList(st, vars, rest1) {
                    case Ok((ctxs, Token.FatArrow :: rest2)) =>
                        Result.map(tyRes -> {
                            let (ty, rest3) = tyRes;
                            ((binders, ctxs, ty), rest3)
                        }, parseType(st, rest2))
                    case _ =>
                        Result.map(tyRes -> {
                            let (ty, rest2) = tyRes;
                            ((binders, Nil, ty), rest2)
                        }, parseType(st, rest1))
                }
            },
            parseOptionalForall(ts)
        )

    def parseOptionalForall(ts: List[Token]): Result[String, (List[SBinder], List[Token])] = match ts {
        case Token.KwForall :: rest =>
            Result.flatMap(
                bindersRes -> {
                    let (binders, rest1) = bindersRes;
                    match rest1 {
                        case Token.Dot :: rest2 => Ok((binders, rest2))
                        case _ => Err("Expected `.` after forall binders.")
                    }
                },
                parseBinderList(rest)
            )
        case _ => Ok((Nil, ts))
    }

    def parseInstanceHeadAndContext(st: SurfaceState, ts: List[Token]): Result[String, ((List[SConstr], (Id, SType)), List[Token])] =
        match tryConstraintList(st, Map.empty(), ts) {
            case Ok((ctxs, Token.FatArrow :: rest1)) =>
                Result.map(
                    headRes -> {
                        let (head, rest2) = headRes;
                        ((ctxs, head), rest2)
                    },
                    parseTraitHead(st, rest1)
                )
            case _ =>
                Result.map(
                    headRes -> {
                        let (head, rest1) = headRes;
                        ((Nil, head), rest1)
                    },
                    parseTraitHead(st, ts)
                )
        }

    def tryConstraintList(st: SurfaceState, vars: Map[Id, Kind], ts: List[Token]): ParseResult[List[SConstr]] =
        Result.flatMap(
            firstRes -> {
                let (first, rest1) = firstRes;
                parseMoreConstraints(st, vars, rest1, first :: Nil)
            },
            parseConstraint(st, vars, ts)
        )

    def parseMoreConstraints(st: SurfaceState, vars: Map[Id, Kind], ts: List[Token], acc: List[SConstr]): ParseResult[List[SConstr]] = match ts {
        case Token.Comma :: rest =>
            Result.flatMap(
                nextRes -> {
                    let (c, rest1) = nextRes;
                    parseMoreConstraints(st, vars, rest1, c :: acc)
                },
                parseConstraint(st, vars, rest)
            )
        case _ => Ok((List.reverse(acc), ts))
    }

    def parseConstraint(st: SurfaceState, _vars: Map[Id, Kind], ts: List[Token]): ParseResult[SConstr] = match ts {
        case Token.Name(name) :: Token.LBracket :: rest =>
            Result.flatMap(
                argRes -> {
                    let (arg, rest1) = argRes;
                    match rest1 {
                        case Token.RBracket :: Token.Tilde :: rest2 =>
                            Result.map(
                                rhsRes -> {
                                    let (rhs, rest3) = rhsRes;
                                    (SConstr.Eq(asHeadType(st, name, arg), rhs), rest3)
                                },
                                parseType(st, rest2)
                            )
                        case Token.RBracket :: rest2 =>
                            if (Map.memberOf(name, SurfaceState.traits(st)))
                                Ok((SConstr.Class(name, arg), rest2))
                            else
                                Err("Unknown trait `${name}` in constraint.")
                        case _ => Err("Expected `]` in constraint.")
                    }
                },
                parseType(st, rest)
            )
        case _ =>
            Result.flatMap(
                leftRes -> {
                    let (lhs, rest1) = leftRes;
                    match rest1 {
                        case Token.Tilde :: rest2 =>
                            Result.map(
                                rhsRes -> {
                                    let (rhs, rest3) = rhsRes;
                                    (SConstr.Eq(lhs, rhs), rest3)
                                },
                                parseType(st, rest2)
                            )
                        case _ => Err("Expected trait constraint or equality constraint.")
                    }
                },
                    parseType(st, ts)
            )
    }

    def parseTraitHead(st: SurfaceState, ts: List[Token]): ParseResult[(Id, SType)] = match ts {
        case Token.Name(name) :: Token.LBracket :: rest =>
            Result.flatMap(
                argRes -> {
                    let (arg, rest1) = argRes;
                    match rest1 {
                        case Token.RBracket :: rest2 => Ok(((name, arg), rest2))
                        case _ => Err("Expected `]` in trait head.")
                    }
                },
                parseType(st, rest)
            )
        case _ => Err("Expected trait head.")
    }

    def parseBinderList(ts: List[Token]): Result[String, (List[SBinder], List[Token])] =
        Result.flatMap(
            firstRes -> {
                let (first, rest1) = firstRes;
                parseMoreBinders(rest1, first :: Nil)
            },
            parseBinder(ts)
        )

    def parseMoreBinders(ts: List[Token], acc: List[SBinder]): Result[String, (List[SBinder], List[Token])] = match ts {
        case Token.Comma :: rest =>
            Result.flatMap(
                nextRes -> {
                    let (next, rest1) = nextRes;
                    parseMoreBinders(rest1, next :: acc)
                },
                parseBinder(rest)
            )
        case _ => Ok((List.reverse(acc), ts))
    }

    def parseBinder(ts: List[Token]): Result[String, (SBinder, List[Token])] = match ts {
        case Token.Name(name) :: rest =>
            Result.map(
                pair -> {
                    let (kind, rest1) = pair;
                    ((name, kind), rest1)
                },
                parseOptionalResultKind(rest, Kind.Star)
            )
        case _ => Err("Expected binder name.")
    }

    def parseOptionalResultKind(ts: List[Token], defaultKind: Kind): Result[String, (Kind, List[Token])] = match ts {
        case Token.Colon :: rest => parseKind(rest)
        case _ => Ok((defaultKind, ts))
    }

    def parseKind(ts: List[Token]): Result[String, (Kind, List[Token])] =
        Result.flatMap(
            lhsRes -> {
                let (lhs, rest1) = lhsRes;
                match rest1 {
                    case Token.Arrow :: rest2 =>
                        Result.map(
                            rhsRes -> {
                                let (rhs, rest3) = rhsRes;
                                (Kind.KFun(lhs, rhs), rest3)
                            },
                            parseKind(rest2)
                        )
                    case _ => Ok((lhs, rest1))
                }
            },
            parseKindAtom(ts)
        )

    def parseKindAtom(ts: List[Token]): Result[String, (Kind, List[Token])] = match ts {
        case Token.KwKindType :: rest => Ok((Kind.Star, rest))
        case Token.KwKindEff :: rest => Ok((Kind.Eff, rest))
        case Token.LParen :: rest =>
            Result.flatMap(
                kindRes -> {
                    let (k, rest1) = kindRes;
                    match rest1 {
                        case Token.RParen :: rest2 => Ok((k, rest2))
                        case _ => Err("Expected `)` after kind.")
                    }
                },
                parseKind(rest)
            )
        case _ => Err("Expected kind.")
    }

    def parseType(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        Result.flatMap(
            lhsRes -> {
                let (lhs, rest1) = lhsRes;
                match rest1 {
                    case Token.Arrow :: rest2 =>
                        Result.flatMap(
                            rhsRes -> {
                                let (rhs, rest3) = rhsRes;
                                match rest3 {
                                    case Token.Backslash :: rest4 =>
                                        Result.map(
                                            effRes -> {
                                                let (efx, rest5) = effRes;
                                                (SType.Fun(lhs, rhs, efx), rest5)
                                            },
                                            parseEffect(st, rest4)
                                        )
                                    case _ => Ok((SType.Fun(lhs, rhs, SType.EffEmpty), rest3))
                                }
                            },
                            parseType(st, rest2)
                        )
                    case _ => Ok((lhs, rest1))
                }
            },
            parseTypeApp(st, ts)
        )

    def parseTypeApp(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        Result.flatMap(
            baseRes -> {
                let ((name, base), rest1) = baseRes;
                match rest1 {
                    case Token.LBracket :: rest2 =>
                        Result.flatMap(
                            argsRes -> {
                                let (args, rest3) = argsRes;
                                match rest3 {
                                    case Token.RBracket :: rest4 =>
                                        let ty = makeBracketType(st, name, base, args);
                                        Ok((ty, rest4))
                                    case _ => Err("Expected `]` after type arguments.")
                                }
                            },
                            parseTypeList(st, rest2)
                        )
                    case _ => Ok((base, rest1))
                }
            },
            parseTypeAtom(st, ts)
        )

    def parseTypeAtom(st: SurfaceState, ts: List[Token]): Result[String, ((Id, SType), List[Token])] = match ts {
        case Token.Name(name) :: rest => Ok(((name, if (isLowerName(name)) SType.Var(name) else SType.Con(name)), rest))
        case Token.LParen :: Token.RParen :: rest => Ok((("", SType.Con("Unit")), rest))
        case Token.LParen :: rest =>
            Result.flatMap(
                tyRes -> {
                    let (ty, rest1) = tyRes;
                    match rest1 {
                        case Token.RParen :: rest2 => Ok((("", ty), rest2))
                        case _ => Err("Expected `)` after type.")
                    }
                },
                parseType(st, rest)
            )
        case _ => Err("Expected type.")
    }

    def parseTypeList(st: SurfaceState, ts: List[Token]): ParseResult[List[SType]] =
        Result.flatMap(
            firstRes -> {
                let (first, rest1) = firstRes;
                parseMoreTypes(st, rest1, first :: Nil)
            },
            parseType(st, ts)
        )

    def parseMoreTypes(st: SurfaceState, ts: List[Token], acc: List[SType]): ParseResult[List[SType]] = match ts {
        case Token.Comma :: rest =>
            Result.flatMap(
                nextRes -> {
                    let (next, rest1) = nextRes;
                    parseMoreTypes(st, rest1, next :: acc)
                },
                parseType(st, rest)
            )
        case _ => Ok((List.reverse(acc), ts))
    }

    def parseEffect(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        parseEffectXor(st, ts)

    def parseEffectXor(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        Result.flatMap(
            lhsRes -> parseEffectXorTail(st, lhsRes, ts),
            parseEffectUnion(st, ts)
        )

    def parseEffectXorTail(st: SurfaceState, lhsRes: (SType, List[Token]), _: List[Token]): ParseResult[SType] = {
        let (lhs, rest1) = lhsRes;
        match rest1 {
            case Token.Caret :: rest2 =>
                Result.flatMap(
                    rhsRes -> parseEffectXorTail(st, (SType.EffXor(lhs, fst(rhsRes)), snd(rhsRes)), rest2),
                    parseEffectUnion(st, rest2)
                )
            case _ => Ok((lhs, rest1))
        }
    }

    def parseEffectUnion(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        Result.flatMap(
            lhsRes -> parseEffectUnionTail(st, lhsRes, ts),
            parseEffectIntersect(st, ts)
        )

    def parseEffectUnionTail(st: SurfaceState, lhsRes: (SType, List[Token]), _: List[Token]): ParseResult[SType] = {
        let (lhs, rest1) = lhsRes;
        match rest1 {
            case Token.Plus :: rest2 =>
                Result.flatMap(
                    rhsRes -> parseEffectUnionTail(st, (SType.EffUnion(lhs, fst(rhsRes)), snd(rhsRes)), rest2),
                    parseEffectIntersect(st, rest2)
                )
            case _ => Ok((lhs, rest1))
        }
    }

    def parseEffectIntersect(st: SurfaceState, ts: List[Token]): ParseResult[SType] =
        Result.flatMap(
            lhsRes -> parseEffectIntersectTail(st, lhsRes, ts),
            parseEffectUnary(st, ts)
        )

    def parseEffectIntersectTail(st: SurfaceState, lhsRes: (SType, List[Token]), _: List[Token]): ParseResult[SType] = {
        let (lhs, rest1) = lhsRes;
        match rest1 {
            case Token.Amp :: rest2 =>
                Result.flatMap(
                    rhsRes -> parseEffectIntersectTail(st, (SType.EffIntersect(lhs, fst(rhsRes)), snd(rhsRes)), rest2),
                    parseEffectUnary(st, rest2)
                )
            case _ => Ok((lhs, rest1))
        }
    }

    def parseEffectUnary(st: SurfaceState, ts: List[Token]): ParseResult[SType] = match ts {
        case Token.Tilde :: rest =>
            Result.map(
                pair -> {
                    let (efm, rest1) = pair;
                    (SType.EffCompl(efm), rest1)
                },
                parseEffectUnary(st, rest)
            )
        case _ => parseEffectAtom(st, ts)
    }

    def parseEffectAtom(st: SurfaceState, ts: List[Token]): ParseResult[SType] = match ts {
        case Token.LBrace :: Token.RBrace :: rest => Ok((SType.EffEmpty, rest))
        case Token.Name(name) :: rest =>
            if (isLowerName(name))
                parseEffectBracketed(st, name, SType.EffVar(name), rest)
            else
                parseEffectBracketed(st, name, SType.EffConst(name), rest)
        case Token.LParen :: rest =>
            Result.flatMap(
                effRes -> {
                    let (efx, rest1) = effRes;
                    match rest1 {
                        case Token.RParen :: rest2 => Ok((efx, rest2))
                        case _ => Err("Expected `)` after effect formula.")
                    }
                },
                parseEffect(st, rest)
            )
        case _ => Err("Expected effect formula.")
    }

    def parseEffectBracketed(st: SurfaceState, name: Id, base: SType, ts: List[Token]): ParseResult[SType] = match ts {
        case Token.LBracket :: rest =>
            Result.flatMap(
                argRes -> {
                    let (arg, rest1) = argRes;
                    match rest1 {
                        case Token.RBracket :: rest2 =>
                            if (Map.memberOf(name, SurfaceState.assocs(st)))
                                Ok((SType.Assoc(name, arg), rest2))
                            else
                                Ok((SType.App(base, arg), rest2))
                        case _ => Err("Expected `]` after effect application.")
                    }
                },
                parseType(st, rest)
            )
        case _ => Ok((base, ts))
    }

    def makeBracketType(st: SurfaceState, name: Id, base: SType, args: List[SType]): SType =
        if (Map.memberOf(name, SurfaceState.assocs(st))) match args {
            case arg :: Nil => SType.Assoc(name, arg)
            case _ => foldApps(base, args)
        } else foldApps(base, args)

    def foldApps(base: SType, args: List[SType]): SType =
        List.foldLeft((acc, arg) -> SType.App(acc, arg), base, args)

    def parseExpr(ts: List[Token]): ParseResult[SExpr] = match ts {
        case Token.Backslash :: Token.Name(name) :: Token.Arrow :: rest =>
            Result.map(
                bodyRes -> {
                    let (body, rest1) = bodyRes;
                    (SExpr.Lam(name, body), rest1)
                },
                parseExpr(rest)
            )
        case Token.KwIf :: rest =>
            Result.flatMap(
                condRes -> {
                    let (cond, rest1) = condRes;
                    match rest1 {
                        case Token.KwThen :: rest2 =>
                            Result.flatMap(
                                thenRes -> {
                                    let (tBranch, rest3) = thenRes;
                                    match rest3 {
                                        case Token.KwElse :: rest4 =>
                                            Result.map(
                                                elseRes -> {
                                                    let (fBranch, rest5) = elseRes;
                                                    (SExpr.IfElse(cond, tBranch, fBranch), rest5)
                                                },
                                                parseExpr(rest4)
                                            )
                                        case _ => Err("Expected `else` in conditional expression.")
                                    }
                                },
                                parseExpr(rest2)
                            )
                        case _ => Err("Expected `then` in conditional expression.")
                    }
                },
                parseExpr(rest)
            )
        case Token.KwRun :: rest =>
            Result.flatMap(
                exprRes -> {
                    let (expr, rest1) = exprRes;
                    match rest1 {
                        case Token.KwWithout :: Token.Name(ef) :: rest2 =>
                            Ok((SExpr.RunWithout(expr, ef), rest2))
                        case _ => Err("Expected `without <Effect>` after `run`.")
                    }
                },
                parseAppExpr(rest)
            )
        case _ => parseAppExpr(ts)
    }

    def parseAppExpr(ts: List[Token]): ParseResult[SExpr] =
        Result.flatMap(
            atomRes -> {
                let (atom, rest1) = atomRes;
                parseAppExprTail(atom, rest1)
            },
            parseExprAtom(ts)
        )

    def parseAppExprTail(lhs: SExpr, ts: List[Token]): ParseResult[SExpr] =
        if (startsExpr(ts))
            Result.flatMap(
                rhsRes -> {
                    let (rhs, rest1) = rhsRes;
                    parseAppExprTail(SExpr.Ap(lhs, rhs), rest1)
                },
                parseExprAtom(ts)
            )
        else Ok((lhs, ts))

    def startsExpr(ts: List[Token]): Bool = match ts {
        case Token.Name(_) :: _ => true
        case Token.IntLit(_) :: _ => true
        case Token.CharLit(_) :: _ => true
        case Token.KwTrue :: _ => true
        case Token.KwFalse :: _ => true
        case Token.KwDo :: _ => true
        case Token.LParen :: _ => true
        case _ => false
    }

    def parseExprAtom(ts: List[Token]): ParseResult[SExpr] = match ts {
        case Token.Name(name) :: rest => Ok((SExpr.Var(name), rest))
        case Token.IntLit(_) :: rest => Ok((SExpr.LitInt32, rest))
        case Token.CharLit(_) :: rest => Ok((SExpr.LitChar, rest))
        case Token.KwTrue :: rest => Ok((SExpr.LitBool(true), rest))
        case Token.KwFalse :: rest => Ok((SExpr.LitBool(false), rest))
        case Token.KwDo :: Token.Name(ef) :: rest => Ok((SExpr.Do(ef), rest))
        case Token.LParen :: Token.RParen :: rest => Ok((SExpr.LitUnit, rest))
        case Token.LParen :: rest =>
            Result.flatMap(
                exprRes -> {
                    let (expr, rest1) = exprRes;
                    match rest1 {
                        case Token.RParen :: rest2 => Ok((expr, rest2))
                        case _ => Err("Expected `)` after expression.")
                    }
                },
                parseExpr(rest)
            )
        case _ => Err("Expected expression.")
    }

    def lowerScheme(st: SurfaceState, binders: List[SBinder], ctxs: List[SConstr], ty: SType): Scheme[Type] = {
        let genEnv = genEnvOf(binders);
        let kinds = List.map(snd, binders);
        let loweredCtx = List.map(lowerConstr(st, genEnv), ctxs);
        let loweredTy = lowerType(st, genEnv, ty);
        Scheme.Scheme(kinds, Qual.Qual(loweredCtx, loweredTy))
    }

    def genEnvOf(binders: List[SBinder]): Map[Id, (Int32, Kind)] =
        let indexed = List.zipWithIndex(binders);
        List.foldLeft(
            (acc, pair) -> {
                let (i, binder) = pair;
                let (name, kind) = binder;
                Map.insert(name, (i, kind), acc)
            },
            Map.empty(),
            indexed
        )

    def binderMap(binders: List[SBinder]): Map[Id, Kind] =
        List.foldLeft(
            (acc, binder) -> Map.insert(fst(binder), snd(binder), acc),
            Map.empty(),
            binders
        )

    def lowerConstr(st: SurfaceState, genEnv: Map[Id, (Int32, Kind)]): SConstr -> Constr = c -> match c {
        case SConstr.Class(name, arg) => Constr.Class(name, lowerType(st, genEnv, arg))
        case SConstr.Eq(lhs, rhs) => Constr.Eq(lowerType(st, genEnv, lhs), lowerType(st, genEnv, rhs))
    }

    def lowerClassHead(st: SurfaceState, head: (Id, SType)): ClassConstr = match head {
        case (name, arg) => (name, lowerType(st, Map.empty(), arg))
    }

    def lowerType(st: SurfaceState, genEnv: Map[Id, (Int32, Kind)], ty: SType): Type = match ty {
        case SType.Var(name) => lowerNamedVar(name, Kind.Star, genEnv)
        case SType.EffVar(name) => lowerNamedVar(name, Kind.Eff, genEnv)
        case SType.Con(name) =>
            Type.Con(Tycon.Tycon(name, lookupTyconKind(name, st)))
        case SType.App(f, x) =>
            Type.Ap(lowerType(st, genEnv, f), lowerType(st, genEnv, x))
        case SType.Assoc(name, arg) =>
            let kind = Option.getWithDefault(Kind.Star, Map.get(name, SurfaceState.assocs(st)));
            Type.Assoc(Tyassoc.Tyassoc(name, lowerType(st, genEnv, arg), kind))
        case SType.Fun(arg, res, ef) =>
            Type.mkArrow(
                lowerType(st, genEnv, arg),
                lowerType(st, genEnv, ef),
                lowerType(st, genEnv, res)
            )
        case SType.EffEmpty => Type.efEmpty()
        case SType.EffConst(name) => Type.efConstant(name)
        case SType.EffUnion(l, r) =>
            Type.mkUnion(lowerType(st, genEnv, l), lowerType(st, genEnv, r))
        case SType.EffIntersect(l, r) =>
            Type.mkIntersect(lowerType(st, genEnv, l), lowerType(st, genEnv, r))
        case SType.EffXor(l, r) =>
            Type.mkXor(lowerType(st, genEnv, l), lowerType(st, genEnv, r))
        case SType.EffCompl(i) =>
            Type.mkCompl(lowerType(st, genEnv, i))
    }

    def lowerNamedVar(name: Id, defaultKind: Kind, genEnv: Map[Id, (Int32, Kind)]): Type =
        match Map.get(name, genEnv) {
            case Some((i, _)) => Type.Gen(i)
            case None => Type.Var(Tyvar.Tyvar(name, defaultKind))
        }

    def lookupTyconKind(name: Id, st: SurfaceState): Kind =
        Option.getWithDefault(Kind.Star, Map.get(name, SurfaceState.tycons(st)))

    def lowerExpr(e: SExpr): Expr = match e {
        case SExpr.Var(name) => Expr.Var(name)
        case SExpr.LitInt32 => Expr.Lit(Type.int32())
        case SExpr.LitBool(_) => Expr.Lit(Type.bool())
        case SExpr.LitChar => Expr.Lit(Type.char())
        case SExpr.LitUnit => Expr.Lit(Type.unit())
        case SExpr.Ap(f, x) => Expr.Ap(lowerExpr(f), lowerExpr(x))
        case SExpr.Lam(name, body) => Expr.Lam(name, lowerExpr(body))
        case SExpr.IfElse(c, t, f) => Expr.IfElse(lowerExpr(c), lowerExpr(t), lowerExpr(f))
        case SExpr.Do(ef) => Expr.Do(ef)
        case SExpr.RunWithout(expr, ef) => Expr.RunWith(lowerExpr(expr), ef)
    }

    def enumKind(binders: List[SBinder]): Kind =
        List.foldRight((binder, acc) -> Kind.KFun(snd(binder), acc), Kind.Star, binders)

    def asHeadType(st: SurfaceState, name: Id, arg: SType): SType =
        if (Map.memberOf(name, SurfaceState.assocs(st))) SType.Assoc(name, arg)
        else SType.App(SType.Con(name), arg)

    def isLowerName(name: String): Bool =
        String.nonEmpty(name) and Char.isLowerCase(String.charAt(0, name))
}
