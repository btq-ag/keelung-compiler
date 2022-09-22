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

newtype Options
  = Protocol ProtocolOptions
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

--------------------------------------------------------------------------------

data ProtocolOptions
  = CompileO0
  | CompileO1
  | CompileO2
  | Interpret
  deriving (Show)

protocol :: Parser ProtocolOptions
protocol =
  hsubparser
    ( command
        "O0"
        ( info
            (pure CompileO0 <**> helper)
            ( fullDesc
                <> progDesc "Compile a Keelung program to R1CS (-O0)"
            )
        )
        <> command
          "O1"
          ( info
              (pure CompileO1 <**> helper)
              ( fullDesc
                  <> progDesc "Compile a Keelung program to R1CS (-O1)"
              )
          )
        <> command
          "O2"
          ( info
              (pure CompileO2 <**> helper)
              ( fullDesc
                  <> progDesc "Compile a Keelung program to R1CS (-O2)"
              )
          )
        <> command
          "interpret"
          ( info
              (pure Interpret <**> helper)
              ( fullDesc
                  <> progDesc "Interpret a Keelung program with given inputs"
              )
          )
    )
