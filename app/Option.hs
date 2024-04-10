module Option (Options (..), getOptions, ProtocolOptions (..)) where

import Options.Applicative

getOptions :: IO Options
getOptions =
  execParser $
    info
      (options <**> helper)
      ( fullDesc
          -- <> progDesc "Print a greeting for TARGET"
          <> header "Keelung - a R1CS compiler"
      )

data Options
  = Protocol ProtocolOptions
  | Version
  deriving (Show)

options :: Parser Options
options =
  hsubparser
    ( command
        "protocol"
        (info (Protocol <$> protocol) (fullDesc <> progDesc "Interal protocol for functions like 'compile' in Keelung"))
        <> commandGroup "Internal binary protocol:"
        <> metavar "PROTOCOL"
    )
    <|> flag' Version (long "version" <> short 'v' <> help "Show version")

--------------------------------------------------------------------------------

data ProtocolOptions
  = CompileO0
  | CompileO1
  | CompileO2
  | Interpret
  | SolveOutput
  | GenCircuit String
  | GenWitness String
  | GenWtns String
  | GenCircuitBin String
  deriving (Show)

protocol :: Parser ProtocolOptions
protocol =
  hsubparser
    ( command
        "O0"
        ( info
            (pure CompileO0 <**> helper)
            ( fullDesc
                <> progDesc "Compiles a Keelung program to R1CS (-O0)"
            )
        )
        <> command
          "O1"
          ( info
              (pure CompileO1 <**> helper)
              ( fullDesc
                  <> progDesc "Compiles a Keelung program to R1CS (-O1)"
              )
          )
        <> command
          "O2"
          ( info
              (pure CompileO2 <**> helper)
              ( fullDesc
                  <> progDesc "Compiles a Keelung program to R1CS (-O2)"
              )
          )
        <> command
          "interpret"
          ( info
              (pure Interpret <**> helper)
              ( fullDesc
                  <> progDesc "Interprets a Keelung program with given inputs"
              )
          )
        <> command
          "solve"
          ( info
              (pure SolveOutput <**> helper)
              ( fullDesc
                  <> progDesc "Solves the R1CS of a Keelung program with given inputs and outputs the result"
              )
          )
        <> command
          "toJSON"
          ( info
              (GenCircuit <$> pathArg "circuit.jsonl" <**> helper)
              ( fullDesc
                  <> progDesc "Compiles (-O1) a Keelung program to R1CS and outputs it as \"circuit.jsonl\""
              )
          )
        <> command
          "genCircuit"
          ( info
              (GenCircuit <$> pathArg "circuit.jsonl" <**> helper)
              ( fullDesc
                  <> progDesc "Compiles (-O1) a Keelung program to R1CS and outputs it as \"circuit.jsonl\""
              )
          )
        <> command
          "genCircuitBin"
          ( info
              (GenCircuitBin <$> pathArg "circuit.r1cs" <**> helper)
              ( fullDesc
                  <> progDesc "Compiles (-O1) a Keelung program to R1CS binary (for Snarkjs and such) and outputs it as \"circuit.r1cs\""
              )
          )
        <> command
          "genWitness"
          ( info
              (GenWitness <$> pathArg "witness.jsonl" <**> helper)
              ( fullDesc
                  <> progDesc "Interprets (-O1) a Keelung program with inputs and outputs the witnesses it as \"witness.jsonl\""
              )
          )
        <> command
          "genWtns"
          ( info
              (GenWtns <$> pathArg "witness.wtns" <**> helper)
              ( fullDesc
                  <> progDesc "Interprets (-O1) a Keelung program with inputs and outputs the witnesses it as Snarkjs' binary format \"witness.wtns\""
              )
          )
    )

pathArg :: String -> Parser String
pathArg defaultPath =
  strOption
    (long "filepath" <> value defaultPath <> metavar "FILEPATH" <> help "File path to store the circuit or witness")