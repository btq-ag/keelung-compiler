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
  | Profile Int Int
  | Count Int Int
  deriving (Show)

options :: Parser Options
options =
  hsubparser
    ( command
        "count"
        (info count (fullDesc <> progDesc "Computes constraint count"))
        <> command
          "profile"
          (info profile (fullDesc <> progDesc "Generates Flamegraphs for profiling"))
        <> commandGroup "Internal Debugging commands:"
        <> metavar "DEBUG"
    )
    <|> hsubparser
      ( command
          "protocol"
          (info (Protocol <$> protocol) (fullDesc <> progDesc "Interal protocol for functions like 'compile' in Keelung"))
          <> commandGroup "Internal binary protocol:"
          <> metavar "PROTOCOL"
      )

--------------------------------------------------------------------------------

data ProtocolOptions
  = ToCS
  | ToR1CS
  | Interpret
  deriving (Show)

protocol :: Parser ProtocolOptions
protocol =
  hsubparser
    ( command
        "toCS"
        ( info
            (pure ToCS <**> helper)
            ( fullDesc
                <> progDesc "Compile a Keelung program to ConstraintSystem"
            )
        )
        <> command
          "toR1CS"
          ( info
              (pure ToR1CS <**> helper)
              ( fullDesc
                  <> progDesc "Compile a Keelung program to R1CS"
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

--------------------------------------------------------------------------------

profile :: Parser Options
profile =
  Profile
    <$> argument auto (metavar "DIM" <> help "Dimension of Falcon")
    <*> argument auto (metavar "SIG" <> help "Number of signatures")

count :: Parser Options
count =
  Count
    <$> argument auto (metavar "DIM" <> help "Dimension of Falcon")
    <*> argument auto (metavar "SIG" <> help "Number of signatures")
