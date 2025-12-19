import System.IO
import System.Environment (getArgs)
import System.Directory (renameFile)
import Control.Monad (when)

-- Function to split the file based on the specified ranges
splitFile :: [(Int, Int)] -> FilePath -> FilePath -> Bool -> IO ()
splitFile ranges inputFile outputFile append = do
    -- Open the input file in read mode
    inputHandle <- openFile inputFile ReadMode
    -- Create a temporary file for writing the modified content
    tempFileHandle <- openFile "tempFile.tmp" WriteMode
    -- Open the output file: either in WriteMode (overwrite) or AppendMode
    outputHandle <- if append 
                     then openFile outputFile AppendMode  -- Append mode
                     else openFile outputFile WriteMode   -- Overwrite mode

    -- Stream the input file line-by-line and process it
    processLines ranges inputHandle 1 tempFileHandle outputHandle

    -- Close all file handles
    hClose inputHandle
    hClose tempFileHandle
    hClose outputHandle

    -- Rename the temporary file to the input file, overwriting it
    renameFile "tempFile.tmp" inputFile

-- Function to process each line of the file
processLines :: [(Int, Int)] -> Handle -> Int -> Handle -> Handle -> IO ()
processLines ranges inputHandle lineNum tempFileHandle outputHandle = do
    eof <- hIsEOF inputHandle
    when (not eof) $ do
        -- Read the next line
        line <- hGetLine inputHandle
        -- Check if the current line number is within any of the ranges
        let isInRange = any (\(start, end) -> lineNum >= start && lineNum <= end) ranges
        if isInRange then do
            -- Write the line to the output file (to be removed)
            hPutStrLn outputHandle line
        else do
            -- Write the line to the temporary file (to keep)
            hPutStrLn tempFileHandle line
        -- Continue processing the next line
        processLines ranges inputHandle (lineNum + 1) tempFileHandle outputHandle

-- Function to parse the range arguments (e.g., [(1, 3), (5, 7)])
parseRanges :: String -> [(Int, Int)]
parseRanges str = map parseRange (wordsWhen (==',') str)

-- Helper function to parse a single range in the form "b-e"
parseRange :: String -> (Int, Int)
parseRange r =
    case break (== '-') r of
        (startStr, '-' : endStr) -> 
            (read startStr, read endStr)
        _ -> error "Invalid range format, expected 'b-e'"

-- Main entry point for running the program
main :: IO ()
main = do
    -- Get command line arguments
    args <- getArgs
    case args of
        -- Check for append flag and then parse ranges and file paths
        ("-a":rangeStrs:inputFile:outputFile:_) -> do
            -- Parse the range strings into actual tuples
            let ranges = parseRanges rangeStrs
            -- Call the splitFile function with the append flag set to True
            splitFile ranges inputFile outputFile True

        -- Default behavior (no append flag)
        (rangeStrs:inputFile:outputFile:_) -> do
            -- Parse the range strings into actual tuples
            let ranges = parseRanges rangeStrs
            -- Call the splitFile function with the append flag set to False (default)
            splitFile ranges inputFile outputFile False

        -- Handle the case where arguments are missing or invalid
        _ -> putStrLn usageMessage

-- Usage message for help section
usageMessage :: String
usageMessage = unlines
    [ "Usage: splitFile <ranges> <input-file> <output-file> [--append]"
    , "  <ranges>     : A comma-separated list of line ranges to remove (e.g., '1-3,5-7')."
    , "  <input-file> : The input file to process. The file will be **edited in place**, and the lines that fall within the specified ranges will be removed."
    , "  <output-file>: The file where the removed lines will be written."
    , "  --append     : Optional flag to append the removed lines to the output file (default is overwrite)."
    , "  If '--append' is not provided, the output file will be overwritten."
    ]

-- Helper function to split a string based on a delimiter (in this case, commas)
wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s = case dropWhile p s of
                  "" -> []
                  s' -> w : wordsWhen p s''
                        where (w, s'') = break p s'

