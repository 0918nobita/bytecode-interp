open System.IO

type VarDecl =
    | VarDecl of name: string * value: string

    override this.ToString() =
        let (VarDecl (name, value)) = this
        $"%s{name} = %s{value}"

type DepsType =
    | Gcc
    | Msvc

    override this.ToString() =
        match this with
        | Gcc -> "gcc"
        | Msvc -> "msvc"

type RuleBlock =
    | RuleBlock of rulename: string * command: string * depfile: option<string> * deps: option<DepsType>

    override this.ToString() =
        let (RuleBlock (rulename, command, depfile, deps)) = this

        let depfile =
            depfile
            |> Option.map (fun depfile -> $"    depfile = %O{depfile}\n")
            |> Option.defaultValue ""

        let deps =
            deps
            |> Option.map (fun deps -> $"    deps = %O{deps}\n")
            |> Option.defaultValue ""

        $"rule %s{rulename}\n    command = %s{command}\n%s{depfile}%s{deps}"

type BuildStmt =
    | BuildStmt of outputs: string array * rulename: string * inputs: string array

    override this.ToString() =
        let (BuildStmt (outputs, rulename, inputs)) = this
        let outputs = String.concat " " outputs
        let inputs = String.concat " " inputs
        $"build %s{outputs}: %s{rulename} %s{inputs}"

type BuildFileContent =
    | BuildFileContent of varDecls: VarDecl array * ruleBlocks: RuleBlock array * buildStmts: BuildStmt array

    override this.ToString() =
        let (BuildFileContent (varDecls, ruleBlocks, buildStmts)) = this
        let varDecls = varDecls |> Array.map string
        let ruleBlocks = ruleBlocks |> Array.map string
        let buildStmts = buildStmts |> Array.map string

        buildStmts
        |> Array.append ruleBlocks
        |> Array.append varDecls
        |> String.concat "\n"
        |> sprintf "%s\n"

let mutable varDecls = List.empty<VarDecl>

let var name value =
    varDecls <- VarDecl(name = name, value = value) :: varDecls

let mutable ruleBlocks = List.empty<RuleBlock>

let rule
    rulename
    (options: {| command: string
                 depfile: option<string>
                 deps: option<DepsType> |})
    =
    ruleBlocks <-
        RuleBlock(rulename = rulename, command = options.command, depfile = options.depfile, deps = options.deps)
        :: ruleBlocks

let mutable buildStmts = List.empty<BuildStmt>

let build outputs rulename inputs =
    buildStmts <-
        BuildStmt(outputs = outputs, rulename = rulename, inputs = inputs)
        :: buildStmts

let run buildFile =
    let content =
        BuildFileContent(
            varDecls = Array.ofList varDecls,
            ruleBlocks = Array.ofList ruleBlocks,
            buildStmts = Array.ofList buildStmts
        )
        |> string

    File.WriteAllText(buildFile, content)
