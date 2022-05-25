module Option (Options (..), getOptions, CompileOptions (..)) where

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
  = Compile CompileOptions
  | Stream
  | Profile Int Int
  | Count Int Int
  deriving (Show)

options :: Parser Options
options =
  parseCompile
    <|> parseStream
    <|> parseProfile
    <|> parseCount

--------------------------------------------------------------------------------

newtype CompileOptions = CompileOptions String
  deriving (Show)

parseCompile :: Parser Options
parseCompile =
  Compile
    <$> subparser
      ( command
          "compile"
          ( info
              (compile <**> helper)
              ( fullDesc
                  <> progDesc "Compile a elaborated .keel file"
                  --   <> header "hello - a test for optparse-applicative"
              )
          )
      )

compile :: Parser CompileOptions
compile =
  CompileOptions
    <$> argument
      auto
      ( metavar "SOURCE"
          <> help "Source Keelung program to compile"
      )

--------------------------------------------------------------------------------

stream :: Parser Options
stream = pure Stream

parseStream :: Parser Options
parseStream =
  subparser
    ( command
        "stream"
        ( info
            (stream <**> helper)
            ( fullDesc
                <> progDesc "DEV: profiling"
            )
        )
    )

--------------------------------------------------------------------------------

profile :: Parser Options
profile =
  Profile
    <$> argument auto (metavar "DIM" <> help "Dimension of Falcon")
    <*> argument auto (metavar "SIG" <> help "Number of signatures")

parseProfile :: Parser Options
parseProfile =
  subparser
    ( command
        "profile"
        ( info
            (profile <**> helper)
            ( fullDesc
                <> progDesc "DEV: profiling"
            )
        )
    )

--------------------------------------------------------------------------------

count :: Parser Options
count =
  Count
    <$> argument auto (metavar "DIM" <> help "Dimension of Falcon")
    <*> argument auto (metavar "SIG" <> help "Number of signatures")

parseCount :: Parser Options
parseCount =
  subparser
    ( command
        "count"
        ( info
            (count <**> helper)
            ( fullDesc
                <> progDesc "DEV: counting"
            )
        )
    )

--------------------------------------------------------------------------------

-- sample :: Parser Options
-- sample =
--   Sample
--     <$> strOption
--       ( long "hello"
--           <> metavar "TARGET"
--           <> help "Target for the greeting"
--       )
--     <*> switch
--       ( long "quiet"
--           <> short 'q'
--           <> help "Whether to be quiet"
--       )
--     <*> option
--       auto
--       ( long "enthusiasm"
--           <> help "How enthusiastically to greet"
--           <> showDefault
--           <> value 1
--           <> metavar "INT"
--       )
