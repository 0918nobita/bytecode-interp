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
    | BuildStmt of outputs: string list * rulename: string * inputs: string list

    override this.ToString() =
        let (BuildStmt (outputs, rulename, inputs)) = this
        let outputs = String.concat " " outputs
        let inputs = String.concat " " inputs
        $"build %s{outputs}: %s{rulename} %s{inputs}"

type BuildFileContent =
    | BuildFileContent of varDecls: list<VarDecl> * ruleBlocks: list<RuleBlock> * buildStmts: list<BuildStmt>

    override this.ToString() =
        let (BuildFileContent (varDecls, ruleBlocks, buildStmts)) = this
        let varDecls = varDecls |> List.map string
        let ruleBlocks = ruleBlocks |> List.map string
        let buildStmts = buildStmts |> List.map string

        buildStmts
        |> List.append ruleBlocks
        |> List.append varDecls
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

let generate buildFile =
    let content =
        BuildFileContent(varDecls = varDecls, ruleBlocks = ruleBlocks, buildStmts = buildStmts)
        |> string

    File.WriteAllText(buildFile, content)
