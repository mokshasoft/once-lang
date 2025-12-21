import qualified Data.ByteString.Char8 as BS
import qualified Data.Map.Strict as Map
import System.IO
import System.Environment (getArgs)  -- Add the missing import
import Control.Monad (when)
import Data.List (sortBy)
import Data.Ord (comparing)

-- Function to process the file and count function usages
countFunctionReferences :: FilePath -> IO ()
countFunctionReferences filePath = do
    -- Open the input file in read mode
    handle <- openFile filePath ReadMode

    -- Initialize a map to store word counts (references and definitions)
    let emptyMap = Map.empty :: Map.Map BS.ByteString Int
    -- Initialize a set to store function definitions
    let emptySet = Map.empty :: Map.Map BS.ByteString Int

    -- Process the file line by line
    (wordCounts, functionDefs) <- processFile handle emptyMap emptySet

    -- Close the file handle
    hClose handle

    -- Calculate the final counts by removing the definitions from the references
    let finalCounts = Map.differenceWith combineCounts wordCounts functionDefs

    -- Sort the final counts by usage (descending order)
    let sortedCounts = sortBy (comparing snd) (Map.toList finalCounts)

    -- Print the results
    mapM_ (putStrLn . show) sortedCounts

-- Function to combine the counts (subtract the definitions from the total counts)
combineCounts :: Int -> Int -> Maybe Int
combineCounts count defs
    | count - defs > 0 = Just (count - defs)
    | otherwise = Nothing

-- Function to process each line of the file
processFile :: Handle -> Map.Map BS.ByteString Int -> Map.Map BS.ByteString Int -> IO (Map.Map BS.ByteString Int, Map.Map BS.ByteString Int)
processFile handle wordCounts functionDefs = go 1 wordCounts functionDefs
  where
    go :: Int -> Map.Map BS.ByteString Int -> Map.Map BS.ByteString Int -> IO (Map.Map BS.ByteString Int, Map.Map BS.ByteString Int)
    go lineNum wc fd = do
        eof <- hIsEOF handle
        if eof then return (wc, fd)
        else do
            -- Read the next line from the file
            line <- BS.hGetLine handle
            -- Process the line to update word counts and function definitions
            let (wc', fd') = processLine line lineNum wc fd
            -- Continue to the next line
            go (lineNum + 1) wc' fd'

-- Process a single line to update counts and definitions
processLine :: BS.ByteString -> Int -> Map.Map BS.ByteString Int -> Map.Map BS.ByteString Int -> (Map.Map BS.ByteString Int, Map.Map BS.ByteString Int)
processLine line lineNum wordCounts functionDefs
    | BS.null line = (wordCounts, functionDefs)  -- Skip empty lines
    | otherwise = case BS.break (== 58) line of  -- 58 is the byte for ':'
        (funcName, _) | BS.null funcName -> (wordCounts, functionDefs)  -- Not a function definition
                      | otherwise -> 
                          -- Update word counts (this will also count the function definitions)
                          (Map.insertWith (+) funcName 1 wordCounts, 
                           Map.insertWith (+) funcName 1 functionDefs)

-- Helper function to convert a map to a sorted list of tuples
sortByFrequency :: Map.Map BS.ByteString Int -> [(BS.ByteString, Int)]
sortByFrequency = sortBy (comparing snd) . Map.toList

-- Main function entry point
main :: IO ()
main = do
    -- Get the file path from command line arguments
    args <- getArgs
    case args of
        [filePath] -> countFunctionReferences filePath
        _ -> putStrLn "Usage: <program> <file-path>"

