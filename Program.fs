module Program

// 全く F# らしさのないコードだが、「ふつうのコンパイラをつくろう」で扱っている
// C♭言語コンパイラの実装をそっくり移植して正常に動作させることを当面の目標としているので許してほしい。
// モジュール単位で、移植作業の終わったものから F# らしいコードにリファクタリングする予定である。

// open System.IO

exception OptionParseException of msg : string

type Options () =
    let mutable _sourceFiles = []
    let mutable _ldArgs = []

    static member Parse argv =
        let opts = Options()
        opts.ParseArgv argv
        opts

    member _.ParseArgv _origArgv =
        // TODO: 移植
        ()

    // member _.PrinUsage (writer : TextWriter) =
        // TODO: 移植
        // writer.WriteLine "Usage: cbc [options] file..."

type Compiler (_programName : string) =
    // TODO: errorHandler の初期化
    member this.CommandMain argv =
        // TODO: 移植
        let _opts = this.ParseOptions();
        ()

    member _.ParseOptions argv =
        try
            Options.Parse argv
        with
        | OptionParseException _msg ->
            // TODO: 移植
            exit 1

[<EntryPoint>]
let main argv =
    let programName = "cbc"
    let _version = "1.0.0"
    Compiler(programName).CommandMain argv
    0
