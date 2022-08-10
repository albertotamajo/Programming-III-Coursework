{-# LANGUAGE DeriveGeneric #-}
{-|
Module      : Challenges
Description : This module provided solutions to the Programming III Haskell CourseWork challenges
Copyright   : (c) Alberto Tamajo, 2021
                  University of Southampton, 2021
Maintainer  : at2n19@soton.ac.uk
Stability   : stable
-}

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (WordSearchGrid,Placement,Posn,Orientation(..),solveWordSearch, createWordSearch,
    LamMacroExpr(..),LamExpr(..),prettyPrint, parseLamMacro,
    cpsTransform,innerRedn1,outerRedn1,compareInnerOuter) where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
-- We import System.Random - make sure that your installation has it installed - use stack ghci and stack ghc
import Data.Char
import Parsing
import Control.Monad
import Data.List
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
import System.IO
import System.Random
import Data.Array
import Control.Applicative

instance NFData Orientation
instance NFData LamMacroExpr
instance NFData LamExpr

-- types for Part I
type WordSearchGrid = [[ Char ]]
type Placement = (Posn,Orientation)
type Posn = (Int,Int)
data Orientation = Forward | Back | Up | Down | UpForward | UpBack | DownForward | DownBack deriving (Eq,Ord,Show,Read,Generic)

-- types for Parts II and III
data LamMacroExpr = LamDef [ (String,LamExpr) ] LamExpr deriving (Eq,Show,Read,Generic)
data LamExpr = LamMacro String | LamApp LamExpr LamExpr  |
               LamAbs Int LamExpr  | LamVar Int deriving (Eq,Show,Read,Generic)

-- END OF CODE YOU MUST NOT MODIFY


-- Grid 
--      A Grid is an array of values of type 'a' which are idexed by
--      values of type 'Posn'.
--
type Grid a = Array Posn a


-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 1 - EXERCISE 1 +++                                                      --

-- solveWordSearch
--      This function takes a list of strings and a square puzzle grid as arguments.
--      It returns a list of tuples where the first element is a string of the provided list
--      of strings and the second element is its placement in the square puzzle grid.
--      
solveWordSearch :: [ String ] -> WordSearchGrid -> [ (String, Maybe Placement) ]

solveWordSearch [] _ = [] 
solveWordSearch xs [] = [(x, Nothing) | x <- xs] -- if the puzzle grid is an empty list then none of the strings in the provided list are present
solveWordSearch xs ws | (replicate (rows) rows /= cols) = error "The grid must be a square"  --checks whether the WordSearchGrid is not a square 
                      | otherwise = ( [(x, Nothing) | x <- xs, x==[]] ) ++ (searchForWordsPosition [] (filter (\x -> x /= []) xs) inds array)  -- empty words are not present in the grid and do not need to be searched.
                        where
                          rows = length ws
                          cols = map length ws
                          array = (listArray ((0,0),(rows-1,rows-1)) (concat ws) )  -- converts the WordSearchGrid into a Grid to improve efficiency
                          inds = indices array
                            
                            
-- searchForWordsPosition
--      This function takes the following arguments (in the same order as they appear in the function type):
--          1) A list of tuples 'ns' which indicate the placement of a word in the grid 'ax'
--          2) A list of words 'xs' 
--          3) A list of positions 'ps'
--          4) A grid 'ax'
--      IMPORTANT: Notice that the above word (words) is used in a figurative
--                 way so that to make this function's description clearer.
--      This function returns the list of tuples 'ns' appened to a list which contains the placement of each word
--      in xs in the grid ax given the positions provided in ps.
--      IMPORTANT: this function does not return multiple placements for a word in xs given it occurs multiple times
--                 in the list. This is done in order to make the algorithm more efficient when only one placement of
--                 each word in xs is needed.
-- 
searchForWordsPosition :: Eq a => [([a], Maybe Placement)] -> [[a]] -> [Posn] -> Grid a -> [([a], Maybe Placement)]
                            
searchForWordsPosition ns [] _ _ = ns -- there are no left words to search in the grid
searchForWordsPosition ns xs [] _ = ns ++ [(x,Nothing) | x <- xs] -- the words in 'xs' do not occur in the grid given the empty list of positions
searchForWordsPosition ns xs ((x,y):ps) ax =  searchForWordsPosition (ns++foundWordsJust) remainingWords ps ax
                                          where
                                            orientsList = map (satisfyingOrientations (==) (x,y) ax) xs  -- a list of lists where each list contains the orientations along which a given word is present in the current position
                                            foundTuples = (filter (\(a,b) -> b /= []) . zip xs ) orientsList  -- keeps only the words that are present
                                            foundWords = foundTuples >>= (\(a,b) -> map ((,)a) b)  -- pairs each word present with all of its orientations 
                                            foundWordsJust = map (\(a,b) -> (a, Just((y,x), b))) foundWords -- constructs the placement for each word. 
                                                                                                            -- IMPORTANT: the position (x,y) is swapped to (y,x) so that the column index comes first
                                            remainingWords = let (q,r) = unzip foundWordsJust in xs \\ q 
 

-- searchForWordsPositions
--      This functions works in a similar way as the function 'searchForWordsPosition' so refer to it for more information.
--      Unlike 'searchForWordsPosition', this function returns all placements of each word in 'xs' in the
--      grid 'ax' given the positions 'ps'.
--
searchForWordsPositions :: Eq a => [([a], Maybe Placement)] -> [[a]] -> [Posn] -> Grid a -> [([a], Maybe Placement)]

searchForWordsPositions ns xs [] _ = ns ++ [(x,Nothing) | x <- xs , let (words, places) = unzip ns in (not.elem x) words ] -- the words in 'xs' that do not occur in the grid as there are no positions left are appended to ns
searchForWordsPositions ns xs ((x,y):ps) ax = searchForWordsPositions (ns++foundWordsJust) xs ps ax
                                            where 
                                              orientsList = map (satisfyingOrientations (==) (x,y) ax) xs  -- a list of lists where each list contains the orientations along which a given word is present in the current position
                                              foundTuples = (filter (\(a,b) -> b /= []) . zip xs ) orientsList  -- keeps only the words that are present
                                              foundWords = foundTuples >>= (\(a,b) -> map ((,)a) b)  -- pairs each word present with all of its orientations 
                                              foundWordsJust = map (\(a,b) -> (a, Just((y,x), b))) foundWords -- constructs the placement for each word. 
                                                                                                              -- IMPORTANT: the position (x,y) is swapped to (y,x) so that the column index comes first.
                     
                                                
-- satisfyingOrientations
--
--      This function returns a list of orientations that are satisfiable.
--      The satisfiability of each orientation is checked by using the function
--      'isSatisfying' given the provided boolean function, initial position, grid 
--      and list. 
--      Thus, for more detials refer to the function 'isSatisfying'.
--
satisfyingOrientations :: (a -> a -> Bool) -> Posn -> Grid a -> [a] -> [Orientation]

satisfyingOrientations f p ax xs = let (orients, posns) = unzip $ (filter (\(a,b) -> b==True) . zip oList) satOrients in orients
                                 where
                                   satOrients = pure (isSatisfying f xs p ax) <*> oList
                                   oList = [Forward, Back,Up, Down, UpForward, UpBack, DownForward, DownBack]
                                                    
                                                
-- isSatisfying
--      This function returns true if the provided list fits in the grid and each element of the list
--       satisfies a certain condition (the boolean binary function provided as argument) with the
--       corresponding element already esisting in the grid. The first element of the list must
--       satisfy the condition with the element in the grid at the provided initial position.
--       Following this, the other elements of the list will be checked againts their corresponding
--       elements in the grid following the orientation provided as argument. 
--
--       If the previous conditions are not satisfied then false is returned.
--
isSatisfying :: (a -> a -> Bool) -> [a] -> Posn -> Grid a -> Orientation -> Bool

isSatisfying f xs p ax o = isSatisfyingAux f xs (Just (ax ! p, p) ) ax o 
                         where
                           isSatisfyingAux :: (a -> a -> Bool) -> [a] -> Maybe (a,Posn) -> Grid a -> Orientation  -> Bool
                                                
                           isSatisfyingAux _ [] _ _ _ = True  -- the empty list satisfies the condition
                           isSatisfyingAux _ _ Nothing _ _ = False  -- the list does not fit in the grid
                           isSatisfyingAux f (x:xs) (Just (a,b)) ax o | f x a = isSatisfyingAux f xs (movePositionGrid b o ax) ax o  -- the current list element satisfies the condition with the given element in the grid 
                                                                      | otherwise = False 
                                                                                                                   
                                                                                
-- movePositionGrid
--      This function takes the following arguments:
--          (1) a starting position
--          (2) an orientation
--          (3) a grid
--      
--      It returns a pair of values in a Maybe context.
--      The first element of the pair is the value of the grid cell reached through 
--      a one-step movement from the starting position along the provided
--      orientation. 
--      The second element of the pair is the position of the cell reached in
--      the grid.
--      If the reached position is not a position of the grid then the function
--      will return Nothing.
--      
movePositionGrid :: Posn -> Orientation -> Grid a -> Maybe (a,Posn)

movePositionGrid p Forward ax | c' <= highestColIndex  = Just (ax ! p', p')
                              | otherwise = Nothing
                                          where
                                            highestColIndex = (snd.snd.bounds) ax
                                            (r',c') = movePosition p Forward
                                            p' = (r',c')
                                            
movePositionGrid p Back ax | c' >= 0 =  Just (ax ! p', p')
                           | otherwise = Nothing
                                       where
                                         (r',c') = movePosition p Back
                                         p' = (r',c')
                                   
movePositionGrid p Up ax | r' >= 0 = Just (ax ! p', p')
                         | otherwise = Nothing
                                     where
                                       (r',c') = movePosition p Up
                                       p' = (r',c')
                                 
movePositionGrid p Down ax | r' <= highestRowIndex = Just (ax ! p', p')
                           | otherwise = Nothing
                                       where
                                         highestRowIndex = (fst.snd.bounds) ax
                                         (r',c') = movePosition p Down
                                         p' = (r',c')
                                
movePositionGrid p UpForward ax | r' >= 0 && c' <= highestColIndex = Just (ax ! p', p')
                                | otherwise = Nothing
                                            where
                                              highestColIndex = (snd.snd.bounds) ax
                                              (r',c') = movePosition p UpForward
                                              p' = (r',c')
                                        
movePositionGrid p UpBack ax | r' >= 0 && c' >= 0 = Just (ax ! p', p')
                             | otherwise = Nothing
                                            where
                                              (r',c') = movePosition p UpBack
                                              p' = (r',c')
                                     
movePositionGrid p DownForward ax | r' <= highestRowIndex && c' <= highestColIndex = Just (ax ! p', p')
                                  | otherwise = Nothing
                                              where
                                                highestColIndex = (snd.snd.bounds) ax
                                                highestRowIndex = (fst.snd.bounds) ax
                                                (r',c') = movePosition p DownForward
                                                p' = (r',c')
                                          
movePositionGrid p DownBack ax | r' <= highestRowIndex && c' >= 0 = Just (ax ! p', p')
                               | otherwise = Nothing
                                           where
                                             highestRowIndex = (fst.snd.bounds) ax
                                             (r',c') = movePosition p DownBack
                                             p' = (r',c')
        

-- movePosition
--
--      This function takes as arguments a starting position and an orientation.
--      It returns a new position resulting from moving one step from the starting
--      position along the provided orientation.
--  
movePosition :: Posn -> Orientation -> Posn

movePosition (r,c) Forward = (r,c+1)
movePosition (r,c) Back = (r,c-1)
movePosition (r,c) Up = (r-1,c)
movePosition (r,c) Down = (r+1,c)
movePosition (r,c) UpForward = (r-1, c+1)
movePosition (r,c) UpBack = (r-1,c-1)
movePosition (r,c) DownForward = (r+1,c+1)
movePosition (r,c) DownBack = (r+1,c-1)

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 1 - EXERCISE 2 +++                                                      --

-- createWordSearch
--      This function takes as argument a list of words and a density.
--      The density refers to the ratio between the total number of 
--      characters in the provided list and the total number of cells
--      in the Word Search Puzzle. 
--      It returns a random WordSearch Puzzle where each of the words in the
--      provided list appear exactly once and whose density is less than
--      the provided density value.
--  
createWordSearch :: [ String ] -> Double -> IO WordSearchGrid

createWordSearch [] _ = error "The list of words is empty"
createWordSearch (x:xs) n | n <= 0 || n > 1 = error "The density cannot be less than or equal to 0 or more than 1"
                          | (or $ map (\x -> length x == 0) (x:xs))  = error "Empty words are not allowed"
                          | and $ map (\x -> length x == 1) (x:xs) = error "A list of single words is not allowed"
                          | or $ map (\x -> x > 1) infixesCount = error "It is not possible to create a grid with no duplicates"
                          | otherwise = do  
                                          shuffledIndices <- shufflelist (indices array)  -- randomly shuffles the positions of the grid
                                          shuffledOrientations <- shufflelist (wherePlaceable emptyValue (head sortedfilteredWords) (head shuffledIndices) array)  -- randomly shuffles all orientations along which the longest word 
                                                                                                                                                                   -- can be placed in given the first position of the list 'shuffledIndices'
                                          grid <- placeWordsRandom emptyValue sortedfilteredWords shuffledIndices shuffledOrientations array  -- randomly places all the words in an emtpy grid
                                          case grid of
                                             Nothing -> do createWordSearch (x:xs) (n/wordsNotPlaceableRatio) -- if it is not possible to place the words in an empty WordSearch puzzle 
                                                                                                              -- then try to place them in one whose uppermost density is lower 
                                                                                                           
                                             Just ax -> if exactlyOnceInGrid emptyValue (x:xs) ax then do -- all words are present exactly once
                                                                                                          filledRandom <- fillEmptiesShortestWordHeuristic emptyValue repetitionsShortestWordHeuristic (x:xs) setChrs ax  -- try to fill the empty cells randomly using the Shortest Word heuristic. 
                                                                                                                                                                                                                          -- Even though, it is not guaranteed to succeed, it is worth trying to use it first because 
                                                                                                                                                                                                                          -- its time complexity is much lower than 'fillEmptiesBacktracking'
                                                                                                          case filledRandom of
                                                                                                             Just ax -> return (toListOfLists ax)  -- all empty cells are filled and there are no duplicate words. The grid is converted into a list of lists
                                                                                                             Nothing -> do 
                                                                                                                          filledGrid <- fillEmptiesBacktracking emptyValue (x:xs) setChrs ax -- fill the empty cells randomly with the characters that appear in the list of words using backtracking
                                                                                                                          case filledGrid of
                                                                                                                             Nothing -> createWordSearch (x:xs) (n/notFillableRatio) -- if it is not possible to fill the empty cells so that no repetitions of words occur then 
                                                                                                                                                                                     -- try with a WordSearch Puzzle whose uppermost density is lower
                                                                                                                                                                                     
                                                                                                                             Just ax -> return (toListOfLists ax) -- the grid is converted into a list of lists
                                                                            
                                                        else do
                                                               createWordSearch (x:xs) (n/duplicateWordsRatio)  -- if the words in the list are placed so that repetition occurs then retry the process 
                                                                                                                -- with an uppermost density which is slightly smaller.
                                      where
                                        filteredWords = (removeReverse .  removeInfixesBD) (x:xs)  -- reverses and infixes (in both direction) are filtered out
                                        leftOut = nub ((x:xs) \\ filteredWords) 
                                        infixesCount = map (\f -> f filteredWords)(map isInfixOfCountBDList leftOut)
                                        hiddenChars = sum (map length (x:xs))  -- total characters present in the list of words
                                        sortedfilteredWords = reverse $ sortBy (\a b -> compare (length a) (length b)) filteredWords  -- the words to be placed i are sorted into descending order according to their lengths
                                        lenLongestWord = length $ head sortedfilteredWords
                                        rowSize = head [x | x <- [(lenLongestWord+2)..], (fromIntegral (hiddenChars) / (fromIntegral x)^2 ) < n ]  -- the size of the row (column) of the WordsSearch puzzle is selected so that 
                                                                                                                                                    -- the resulting density is less than the provided one
                                        setChrs = nub (concat (x:xs)) 
                                        emptyValue = head ((map chr [1..]) \\ setChrs)  -- a char that does not occur in the list of words
                                        array = emptyGrid emptyValue rowSize rowSize  -- an empty grid is created which resembles the WordSearch puzzle
                                        wordsNotPlaceableRatio = 2 
                                        duplicateWordsRatio = 1.01
                                        notFillableRatio = 1.5
                                        repetitionsShortestWordHeuristic = 5
     
                                                                                                
-- placeWordsRandom
--      This function takes the following arguments:
--          1) An empty value (all the cells in the grid that contain the empty value are considered empty cells)
--          2) A list of words to be placed in a grid
--          3) A list of positions where the first word in the list may be placed in
--          4) A list of orientations along which the first word in the list can be placed in given the first position in the list of positions
--          5) The grid where to place all words
--      IMPORTANT: Notice that the above word (words) is used in a figurative
--                 way so that to make this function's description clearer. In fact, the first 
--                 argument is any value and the second argument is a list of lists of the same type of the first argument.
--      This function adopts a depth-first search backtracking procedure so that to randomly place all the words provided in the grid. If it is
--      possible to place all words then the grid is returned inside a Just context which is wrapped in turn into an IO context. Otherwise, Nothing
--      wrapped in an IO context will be returned.        
--      This funtion is guaranteed to return a grid with all words placed inside if it is possible to do so as it uses backtracking.
--                                        
placeWordsRandom :: (Eq a, Show a) => a -> [[a]] -> [Posn] -> [Orientation] -> Grid a -> IO (Maybe (Grid a))

placeWordsRandom _ [] _ _ ax = return (Just ax) -- all words are placed
placeWordsRandom _ _ [] _ _ = return Nothing  -- not possible to place all words
placeWordsRandom emptyValue (x:xs) (p:[]) [] ax = placeWordsRandom emptyValue (x:xs) [] [] ax  -- not possible to place the current word as there are no orientations along which to place it in the only one available position

placeWordsRandom emptyValue (x:xs) (p:p':ps) [] ax = do  -- no orientations available for the current word to be placed in the current position
                                                       shuffledOrientations <-shufflelist $ wherePlaceable emptyValue x p' ax  -- randomly shuffle the orientations along which the current word can be placed in the next position 
                                                       placeWordsRandom emptyValue (x:xs) (p':ps) shuffledOrientations ax
                                                    
placeWordsRandom emptyValue (x:[]) (p:ps) (o:os) ax = let updatedGrid = updateGrid x p o ax in  placeWordsRandom emptyValue [] [] [] updatedGrid  -- the last word is placed in the grid

placeWordsRandom emptyValue (x:x':xs) (p:ps) (o:os) ax =  do      
                                                            shuffledSuitableIndices <- shufflelist suitableIndices  -- randomly shuffle the positions where the next word can be placed in
                                                            case shuffledSuitableIndices of
                                                               [] -> placeWordsRandom emptyValue (x:x':xs) (p:ps) os ax  -- if the next word cannot be placed anywhere then try to place the current word along another orientation of the current position
                                                               (p':ps') -> do
                                                                             shuffledOrientations <- shufflelist $ wherePlaceable emptyValue x' p' updatedGrid  -- randomly shuffle the orientations along which the next word can be placed in the next position
                                                                             grid <- placeWordsRandom emptyValue (x':xs) shuffledSuitableIndices shuffledOrientations  updatedGrid
                                                                             case grid of
                                                                                Just ax -> return (Just ax) -- placing all the other subsequent words is successful
                                                                                Nothing -> placeWordsRandom emptyValue (x:x':xs) (p:ps) os ax  -- if it is not possible to place all words given the placement of the current word then try to place it along 
                                                                                                                                               -- another orientation of the current position
                                                                                               
                                                      where
                                                        updatedGrid = updateGrid x p o ax  -- grid with the word x added in position p along orientation o
                                                        suitableIndices = let (indices, values) = unzip $ filter (\(a,b) -> b == emptyValue || b==(head x')) (assocs updatedGrid) in indices    -- positions where the next word may be placed in                                                                   


-- fillEmptiesBacktracking
--      This function takes as arguments an empty values, a list of words, a list of characters and a grid.
--      IMPORTANT: Notice that the above words (characters, words) are used in a figurative
--                 way so that to make this function's description clearer. In fact, the first 
--                 argument is a list of lists and the second is a list of values.
--      This function tries to fill all the empty cells (cells containing the empty value) of the provided grid with a random
--      character inside the list of characters so that not to create duplicates of the words provided.
--      If it is possibe to do so then the filled grid is returned inside a Just context which is wrapped 
--      in turn into an IO context. Otherwise, Nothing wrapped in an IO context will be returned.
--      This function is guaranteed to return a grid with no empty cells and duplicates of words if it is possible to do so as
--      it uses backtracking.
--
fillEmptiesBacktracking :: (Eq a, Show a) => a -> [[a]] -> [a] -> Grid a -> IO (Maybe (Grid a))

fillEmptiesBacktracking emptyValue xs chrs ax = do
                            shuffledCharsPos <- sequence $ replicate (length emptyCells) (shufflelist chrs)  -- creates as many shuffled lists of the possible usable characters as the number of empty cells
                            let shuffledCharsCells = zip emptyCells shuffledCharsPos  -- each empty cell of the grid is matched with a shuffled list of the possible usable characters
                            let arrShuffles =  array (bounds ax) ([ (i,[])| i <- indices ax, (not.elem i) emptyCells] ++ shuffledCharsCells)  -- in order to improve efficiency an array is used to store 'shuffledCharsCells'
                            let currentPlacements = searchForWordsPositions [] xs (indices ax \\ emptyCells) ax  -- the current placements of the words present in the grid
                            fillEmptiesAuxiliary xs emptyCells (arrShuffles ! (head emptyCells)) arrShuffles ax
                                where
                                    emptyCells = lookupIndices emptyValue ax
                                    
                                    fillEmptiesAuxiliary :: (Eq a, Show a) => [[a]] -> [Posn] -> [a] -> Array Posn [a] -> Grid a -> IO (Maybe (Grid a))
                                    
                                    fillEmptiesAuxiliary _ [] _ _ ax = return (Just ax)  -- all empty cells are filled
                                    fillEmptiesAuxiliary _ _  [] _ _  = return Nothing  -- not possible to fill the current empty cell with any character
                                    fillEmptiesAuxiliary xs (p:ps) (c:chrs) arr ax = do 
                                                                                 case not duplicated of
                                                                                    False -> fillEmptiesAuxiliary xs (p:ps) chrs arr ax  -- not possible to place character 'c' as a duplicate word is created. Try with the next possible character
                                                                                    True -> do  
                                                                                              if ps == [] then fillEmptiesAuxiliary xs [] [] arr updatedGrid  -- all emty cells have been filled
                                                                                              else
                                                                                                  do
                                                                                                    grid <- fillEmptiesAuxiliary xs ps (arr ! (head ps) ) arr updatedGrid
                                                                                                    case grid of
                                                                                                       Nothing -> fillEmptiesAuxiliary xs (p:ps) chrs arr ax  -- not possible to fill all empty cells without creating duplicates given the current cell is filled with 'c'. 
                                                                                                                                                              -- Try with the next possible character.
                                                                                                       Just ax -> return (Just ax) 
                                                                            where
                                                                                updatedGrid = ax // [(p,c)]  -- the grid is updated filling the current empty cell
                                                                                allPos = map (\(x:y:[]) -> ((take ((length x) -1) . reverse) x ++ y )) (splitAtEach (allPositionsInOrientations p ((snd.bounds) updatedGrid)) 2)  -- all positions reachable from the current position along all orientations
                                                                                allPosInfixesWithp = concat $ map (allInfixesWithElem p) allPos  -- all infixes of these positions along an orientation including the current position for all orientations
                                                                                possDuplicates = map (positionsToValues updatedGrid) allPosInfixesWithp  -- trasnsforms the above list replacing all positions with the value that the contain in the grid
                                                                                duplicated = or $ map (\ys -> ys `elem` xs || (reverse ys) `elem` xs ) possDuplicates  -- true if a duplicate of a word is created placing the character in the current empty cell. Otherwise, false                                                                                
                       

-- fillEmptiesShortestWordHeuristic    
--      This function takes as argument an empty value, an integer number, a list of words,
--      a list of characters and a grid.     
--      IMPORTANT: Notice that the above words (characters, words) are used in a figurative
--                 way so that to make this function's description clearer. In fact, the first 
--                 argument is a list of lists and the second is a list of values.
--      This function tries to fill all the empty cells (cells containing the empty value) of the provided grid with a random
--      character inside the list of characters so that not to create duplicates of the words provided. This is done combining the 
--      'fillRandom' function and the Shortest-Word Heuristic. In other words, at each iteration of this function a number of empty
--      cells equal to the length of the grid's row times the length of the shortest word are filled using 'fillRandom'.
--      At each iteration of this function, 'fillRandom' will try a number of trials equal to the integer number provided as argument.
--      This function is not guaranteed to return a grid with no empty cells and duplicates of words if it is possible to do so 
--      because it is purely random. However, it is very likely to return a grid with no empty cells when the number of words is up to 50.
--
fillEmptiesShortestWordHeuristic :: (Eq a, Show a) => a -> Int -> [[a]] -> [a] -> Grid a -> IO (Maybe (Grid a))

fillEmptiesShortestWordHeuristic emptyValue n xs chrs ax = fillEmptiesShortestWordHeuristicAux units ax
                              where
                                emptyCells = lookupIndices emptyValue ax
                                pos = indices ax
                                sortedWords = sortBy (\a b -> compare (length a) (length b)) xs  -- the words to be placed are sorted into descending order according to their lengths
                                lenShortestWord = length $ head sortedWords
                                rowSize = round (sqrt $ fromIntegral (length $ pos)) 
                                units = (splitAtEach emptyCells (rowSize *  lenShortestWord))  -- a list of unit of positions
                                
                                -- This function tries to randomly fill all units of positions without creating word duplicates
                                --
                                fillEmptiesShortestWordHeuristicAux [] ax = return (Just ax) 
                                fillEmptiesShortestWordHeuristicAux (r:rs) ax = do
                                                                                  grid <- fillRandom emptyValue n xs chrs r ax
                                                                                  case grid of 
                                                                                     Nothing -> return Nothing  -- filling the current unit of positions has not been successful
                                                                                     Just ax -> fillEmptiesShortestWordHeuristicAux rs ax  -- try to fill the next unit of positions


-- fillRandom
--      This function takes as argument an empty value, an integer number, a list of words,
--      a list of characters, a list of positions and a grid.
--      IMPORTANT: Notice that the above words (characters, words) are used in a figurative
--                 way so that to make this function's description clearer. In fact, the first 
--                 argument is a list of lists and the second is a list of values.
--      This function tries to fill all the provided cell positions in the provided grid with a random
--      character inside the list of characters so that not to create duplicates of the words provided.
--      Since, this function is purely random, it may happen that the grid resulting from randomly fill
--      the provided cell positions contains duplicates of the words. This is why an integer number is provided
--      as argument as it indicates the max number of trials to fill the provided cell positions randomly.
--      If the function succeeds in a trial then the filled grid is returned inside a Just context which is wrapped 
--      in turn into an IO context. Otherwise, Nothing wrapped in an IO context will be returned.
--      This function is not guaranteed to return a grid with no empty cells and duplicates of words if it is possible to do so 
--      because it is purely random.
--
fillRandom :: (Eq a, Show a) => a -> Int -> [[a]] -> [a] -> [Posn] -> Grid a -> IO (Maybe (Grid a))

fillRandom _ 0 _ _ _ _= return Nothing  -- no trials left
fillRandom emptyValue n xs chrs ps ax = do
                                          seq <- shufflelist possibleSequence  -- random characters for the cell positions
                                          let update = zip ps seq
                                          let updatedGrid = ax // update
                                          if exactlyOnceInGrid emptyValue xs updatedGrid then return (Just updatedGrid)  -- no duplicates of words are created
                                          else fillRandom emptyValue (n-1) xs chrs ps ax
                                     where
                                       possibleSequence = take (length ps) $ (concat . replicate (length ps)) chrs
                                                    
                                                    
-- wherePlaced 
--      This function given a list and its placement returns a tuple indicating its
--      starting position and ending position in a grid.
--
wherePlaced :: ([a],Maybe Placement) -> (Posn,Posn)

wherePlaced (_ , Nothing) = error "Not possible to infer the starting and ending position"
wherePlaced (xs, Just (p,o)) = (p, allPos !! ((length xs)-1))
                             where
                               allPos = (iterate (\x -> movePosition x o) p)


-- positionsToValues
--      This function, given a grid and a list of positions, returns
--      a list containing the values contained at each of the positions
--      provided. 
--      
positionsToValues :: Grid a -> [Posn] -> [a]

positionsToValues ax ps = map (ax !) ps


-- allPositionsInOrientations
--      This function returns a list of reacheable positions for each of the possible
--      orientations starting from the provided position and given the max row 
--      and column index of a grid.
--
allPositionsInOrientations :: Posn -> (Int,Int) -> [[Posn]]

allPositionsInOrientations p (r,c) = map (allPositionsInOrientation p (r,c)) ors
                                   where
                                     ors = [Up,Down,Back,Forward, UpBack,DownForward,DownBack,UpForward]


-- allPositionsInOrientation
--      This function returns a list of reacheable positions starting from the 
--      given position along the given orientation and given the max row and column
--      index of the grid.
-- 
allPositionsInOrientation :: Posn -> (Int,Int) -> Orientation -> [Posn]

allPositionsInOrientation p (r,c) o@Forward = takeWhile (\(a,b) -> b <= c)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@Up = takeWhile (\(a,b) -> a >= 0)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@Down = takeWhile (\(a,b) -> a <= r)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@Back = takeWhile (\(a,b) -> b >= 0)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@UpForward = takeWhile (\(a,b) -> b <= c && a >= 0)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@UpBack = takeWhile (\(a,b) -> b >= 0 && a >= 0)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@DownForward = takeWhile (\(a,b) -> b <= c && a <= r)(iterate (\x -> movePosition x o) p)
allPositionsInOrientation p (r,c) o@DownBack = takeWhile (\(a,b) -> b >= 0 && a <= r)(iterate (\x -> movePosition x o) p)

         
-- chooseRandomPair 
--      This function ramdomly chooses a position and one element in
--      its associated list from a list of tuples.
--
chooseRandomPair :: [(a,[b])] ->  IO (a,b)

chooseRandomPair [] = error "No elements in first list"
chooseRandomPair xs  = do
                         n <- randomRIO (0, (length xs) - 1)
                         let (y,ys) = xs !! n  
                         n' <- randomRIO (0, (length ys) -1)
                         return (y, ys !! n')
                            
                            
-- listElementsPositions
--      This function returns the positions of the elements of a list in a grid
--      starting from the given position along the given orientation.
--
listElementsPositions :: ([a], Posn, Orientation) -> [Posn]

listElementsPositions (xs,p,o)  = take (length xs) (iterate (\x -> movePosition x o) p)
                                               
                   
-- exactlyOnceInGrid 
--      This function checks whether every list in a list of lists is
--      placed exactly once in a grid.
--
exactlyOnceInGrid :: Eq a => a -> [[a]] -> Grid a -> Bool

exactlyOnceInGrid _ [] _ = False
exactlyOnceInGrid emptyValue (x:xs) ax | (length positionsList > ((length (x:xs)) + numberPalindromes + 7*numberSingleWords)) || (or $ map (\(a,b) -> b == Nothing) positionsList) = False  -- if there are palindromes then these are counted twice from the 'searchForWordsPositions' function 
                                                                                                                                                                       -- even though they are placed exactly once.
                                                                                                                                                                       -- If there are duplicates or some list is not present in the grid then not all lists are placed exactly once.
                                       
                                       | otherwise = True   -- all lists placed exactly once                                                                            
                                       where
                                         numberPalindromes = sum $  map (\x -> if x==reverse x && length x > 1 then 1 else 0) (x:xs)
                                         positionsList = searchForWordsPositions [] (x:xs) ((indices ax) \\ (lookupIndices emptyValue ax)) ax  -- placements of the lists in the grid. There is no need of scanning the empty cells.
                                         numberSingleWords = sum $ map (\x -> if length x == 1 then 1 else 0) (x:xs)
                    

-- emptyGrid
--      This function creates an nxm empty grid. 
--      'n' is the first provided argument and 'm' is the second one.
--      An empty grid is a grid filled with the empty value of a given
--      instance of the EmptyValue class.
--
emptyGrid :: a -> Int -> Int -> Grid a

emptyGrid emptyValue r c =  listArray ((0,0),(r-1, c-1)) [emptyValue | _ <- [1..(r*c)]]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
         
-- lookupIndices
--      This function takes as arguments a value and a grid.
--      It returns a list of all indices where the provided value
--      occurs in the provided grid.
--
lookupIndices :: Eq a => a -> Grid a -> [Posn]

lookupIndices x ax = let (indices,values) = (unzip . filter (\(a,b) -> b==x )) assos in indices
                   where
                     assos = assocs ax
                                                                    

-- toListOfLists
--      This function takes as argument a grid and transforms it into
--      a corresponding list of lists.
--
toListOfLists :: Grid a -> [[a]]

toListOfLists ax = splitAtEach r cols
                 where
                   (q,r) = (unzip . assocs) ax
                   cols = ((snd . snd. bounds) ax) +1 
               
               
-- splitAtEach
--      This function returns a list of lists by partitioning
--      a given list into subsequent partitions whose size is
--      the provided integer number. When the length of the list
--      is not a multiple of the provided integer number then the 
--      last partition size will be less than the provided number.
--          %%EXAMPLE 1:
--                  splitAtEach [1,2,3,4,5,6,] 3 = [[1,2,3],[4,5,6]]
--          %%EXAMPLE 2:
--                  splitAtEach [1,2,3,4,5,6,] 4 = [[1,2,3,4],[5,6]]
--
splitAtEach :: [a] -> Int -> [[a]]

splitAtEach [] _ = []
splitAtEach xs n = (take n xs) : (splitAtEach (drop n xs) n)    


-- wherePlaceable
--      This function takes as arguments a list, a starting position and a grid.
--
--      It returns a list of orientations that allow the provided list to be placed
--      in the grid from the starting position along the provided orientation without
--      deleting previously placed elements in the grid and ensuring that the whole
--      list fits in the grid along that orientation.
--
wherePlaceable :: Eq a => a -> [a] -> Posn -> Grid a -> [Orientation]

wherePlaceable emptyValue xs p  ax = satisfyingOrientations (\x -> \y ->  y == emptyValue || x==y) p ax xs


-- updateGrid
--      This function takes as arguments a list, a position, an orientation and a grid.
--
--      It returns the same grid updated with the provided list placed from the starting position
--      along the provided orientations.
--      
updateGrid :: [a] -> Posn -> Orientation -> Grid a -> Grid a

updateGrid xs p o ax = let (posns,orients) = unzip $ iterate (\(a,b) -> (movePosition a b, b)) (p,o) in ax // (zip posns xs) 


-- shufflelist
--      This function takes as argument a list and randomly shuffles it.
--      It uses the perfect shuffle algorithm.
--
shufflelist :: [a] -> IO [a]

shufflelist [] = return []
shufflelist xs = (sequence (map randomRIO [(0, len -i) | i <- [1..(len-1)]])) >>= (\x -> return (shuffle1 xs x))
               where
                 len = length xs
                 
                 
-- allInfixesWithElem
--      This function takes a value and a list and returns all the possible infixes
--      of the list where the provided value occurs.
--          %%EXAMPLE 1:
--                  allInfixesWithElem 1 [2,3,1] = [[2,3,1],[3,1],[1]]
--          %%EXAMPLE 2:
--                  allInfixesWithElem 1 [1,2,3] = [[1,2,3]]
--
allInfixesWithElem :: Eq a => a -> [a] -> [[a]]

allInfixesWithElem x xs = case elemIndex x xs of
                             Nothing -> error "Element provided is not in the list"
                             Just index -> auxiliary index xs
                        where
                          len = length xs
                          
                          auxiliary :: Int -> [a] -> [[a]]
                          
                          auxiliary 0 xs = filter (not.null) (inits xs)  -- the element to be included is at the beginning of the list. 
                          auxiliary i (x:xs) = [take y (x:xs) |y <- [(i+1)..(len+1)]] ++ (auxiliary (i-1) xs) 
                                             where
                                               len = length xs
                                          
                                                        
-- allInfixes
--      This function takes as input a string and returns all
--      of its infixes.
--      %%EXAMPLE:
--              allInfixes [1,2,3] = [[1],[1,2],[1,2,3],[2],[2,3],[3]]
--
allInfixes :: [a] -> [[a]]

allInfixes [] = []
allInfixes (x:xs) = (filter (not.null) (inits (x:xs))) ++ (allInfixes xs)
                        
                        
-- isInfixOfAny
--      This function checks whether a list is an infix of another list
--      inside a list of lists.
--          %%EXAMPLE 1:
--                  isInfixOfAny "ban" ["hello","banana"] = True
--          %%EXAMPLE 2:
--                  isInfixOfAny "ban" ["hello","peace"] = False
--
isInfixOfAny :: Eq a => [a] -> [[a]] -> Bool

isInfixOfAny [] _ = False
isInfixOfAny x xs = or $ map (isInfixOf x) xs


-- isInfixOfAnyBD
--      This function works in a similar way as the function 'isInfixOfAny'
--      so refer to it for more info. However, this function checks whether
--      a list is an infix of another list or an ifix of another list's reverse
--      inside a list of lists.
--          %%EXAMPLE 1:
--                  isInfixOfAnyBD "ban" ["hello","naber"] = True
--         %%EXAMPLE 2:
--                  isInfixOfAny "ban" ["hello","banana"] = True  
--         %%EXAMPLE 3:
--                  isInfixOfAny "ban" ["hello","peace"] = False
--
isInfixOfAnyBD :: Eq a => [a] -> [[a]] -> Bool

isInfixOfAnyBD [] _ = False
isInfixOfAnyBD x xs = or $ map (\y -> isInfixOf x y || isInfixOf x (reverse y)) xs


-- countBD
--      This function returns the number of times a list is contained in a list of
--      lists. A list is contained in another list of lists if either it or its
--      reverse appear in the list.
--          %%EXAMPLE 1:
--                  countBD "ban" ["nab","ban"] = 2
--          %%EXAMPLE 2:
--                  countBD "ban" ["banana","naber"] = 0
--          %%EXAMPLE 3:
--                  countBD "ban" ["ban","apple"] = 1
--
countBD:: Eq a => [a] -> [[a]] -> Int

countBD ns xs = foldr (\x -> if ns == x || ns == (reverse x) then (+1) else id) 0 xs


-- isInfixOfCountBD
--      This function counts the number of times a list is an infix of another list
--      and an infix of the other list's reverse.
--          %%EXAMPLE 1:
--                  isInfixOfCountBD "ban" "banana" = 1
--          %%EXAMPLE 2:
--                  isInfixOfCountBD "ban" "bannab" = 2
--          %%EXAMPLE 2:
--                  isInfixOfCountBD "ban" "apple" = 0
--
isInfixOfCountBD :: Eq a => [a] -> [a] -> Int

isInfixOfCountBD x xs = countBD x (allInfixes xs)


-- isInfixOfCountBDList
--      This function returns the sum of the number of times
--      a list is an infix of a list and an infix of the list's
--      reverse in a given list of lists.
--          %%EXAMPLE 1:
--                  isInfixOfCountBDList "ban" ["banana","banner"] = 2
--          %%EXAMPLE 2:
--                  isInfixOfCountBD "ban" ["banana","banner","bannab"] = 4
--          %%EXAMPLE 3:
--                  isInfixOfCountBD "ban" ["apple"] = 0
--
isInfixOfCountBDList :: Eq a => [a] -> [[a]] -> Int

isInfixOfCountBDList x xs = sum $ map (isInfixOfCountBD x) xs


-- isInfixOfAnyCount
--      This function counts the number of lists in a list of lists
--      such that the given list is an infix of them.
--          %%EXAMPLE 1:
--                  isInfixOfAnyCount "ban" ["banana","banner"] = 2
--          %%EXAMPLE 2:
--                  isInfixOfAnyCount"ban" ["banana","banner","bannab"] = 3
--          %%EXAMPLE 3:
--                  isInfixOfAnyCount "ban" ["apple] = 0
--
isInfixOfAnyCount :: Eq a => [a] -> [[a]] -> Int

isInfixOfAnyCount [] _ = 0
isInfixOfAnyCount x xs = length onlyTrues
                       where
                         bools = map (isInfixOf x) xs
                         onlyTrues = filter (\x -> x==True) bools 
                            

-- removeInfixes
--      This function removes all lists in a list of lists such that they are 
--      infixes of other lists in the same list of lists.
--      It behaves similarly to 'nub' in Data.List removing duplicates as well.
--          %%EXAMPLE 1:
--                  removeInfixes ["ban","banana","peach"] = ["banana","peach"]
--          %%EXAMPLE 2:
--                  removeInfixes ["ban","banana","banana","peach"] = ["banana","peach"]
--          
removeInfixes :: Eq a => [[a]] -> [[a]]

removeInfixes  [] = []
removeInfixes  xs = let (notInfixes,r)= (unzip . filter (\(a,b) -> b==False)) $ zip uniques bools in notInfixes 
                  where
                    uniques = nub xs
                    bools = map (\x -> isInfixOfAny x (delete x uniques)) uniques


-- removeInfixesBD
--      This function removes all lists in a list of lists such that they are
--      infixes of other lists or infixes of other lists' reverse in the same 
--      list of lists.
--      It works in a similar way as 'removeInfixes' with the additional feature
--      that a list is considered to be an infix of another list if it is an infix
--      of it or its reverse.
--          %%EXAMPLE 1:
--                  removeInfixesBD ["ban","banana","peach"] = ["banana","peach"]
--          %%EXAMPLE 2:
--                  removeInfixesBD ["ban","banana","banana","peach"] = ["banana","peach"]     
--          %%EXAMPLE 3:
--                  removeInfixesBD ["ban","naber","peach"] = ["naber","peach"] 
--
removeInfixesBD :: Eq a => [[a]] -> [[a]]

removeInfixesBD [] = []
removeInfixesBD xs  = removedInfixesBD
                   where
                     uniques = sortBy (\a b -> compare (length a) (length b)) ( nub xs)
                     succElements = successors1 uniques
                     bools = map (\(a,b) -> isInfixOfAnyBD a b) succElements
                     (removedInfixesBD, _) = unzip $  filter (\(a,b) -> b == False)(zip uniques bools)
                     
                     
-- removeReverse
--      This function removes the lists that are the reverse of another list
--      inside a list of lists.
--      The first occurence of a list which is the reverse of another one
--      is removed from the list.
--          %%EXAMPLE 1:
--                  removeReverse ["bool","loob","ben"] = ["loob","ben"]
--          %%EXAMPLE 2:
--                  removeReverse ["bool","ben"] = ["bool","ben"]
--
removeReverse :: Eq a => [[a]] -> [[a]] 

removeReverse [] = []
removeReverse xs | (last xs) `elem` removedReverse = removedReverse
                 | otherwise = removedReverse ++ [(last xs)]
                 where
                   Just succElements = sequence $  map (\x -> successors x xs) xs
                   bools = map (\(f,xs) -> or $ map f xs) (zip (map isReverse xs) succElements) 
                   removedReverse = (map fst . filter (\(a,b) -> b == False)) (zip xs bools)
               
               
-- successors
--      This function returns the successors of the first occurence of an element 
--      inside a list given that the element belongs to the list. 
--      Otherwise, Nothing is returned.
--          %% EXAMPLE 1:
--                  successors 3 [4,3,1,2,4] = Just [1,2,4]
--          %% EXAMPLE 2:
--                  successors 0 [4,3,1,2,4] = Nothing
--
successors :: Eq a => a -> [a] -> Maybe [a]

successors x xs = elemIndex x xs >>= (\y -> return (drop (y+1) xs))


-- successor1
--      This function returns a list of tuples where the second element
--      is a list of elements that are successors of the first element
--      given a provided list.
--
successors1 :: [a] -> [(a,[a])]

successors1 [] = []
successors1 (x:xs) = (x,xs) : successors1 xs

-- isReverse
--      This function checks whether a list is
--      the reverse of another list.
--          %%EXAMPLE 1:
--                  isReverse "bool" "loob" = True
--          %%EXAMPLE 2:
--                  isReverse "bool" "ben" = False
--
isReverse :: Eq a => [a] -> [a] -> Bool

isReverse x y = reverse x == y
                   

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                             PERFECT SHUFFLE HASKELL ALGORITHM http://okmij.org/ftp/Haskell/perfect-shuffle.txt                              -- 

-- Here the perfect shuffle algorithm taken from http://okmij.org/ftp/Haskell/perfect-shuffle.txt starts

-- ** Efficient implementation based on complete binary trees

--The following is a more sophisticated algorithm:

-- A complete binary tree, of leaves and internal nodes.
-- Internal node: Node card l r
-- where card is the number of leaves under the node.
-- Invariant: card >=2. All internal tree nodes are always full.
data Tree a = Leaf a | Node !Int (Tree a) (Tree a) deriving Show

-- Convert a non-empty sequence (e1...en) to a complete binary tree
build_tree = grow_level . (map Leaf)
    where
    grow_level [node] = node
    grow_level l = grow_level $ inner l
         
    inner [] = []
    inner x@[_] = x
    inner (e1:e2:rest) = (join e1 e2) : inner rest
         
    join l@(Leaf _)       r@(Leaf _)       = Node 2 l r
    join l@(Node ct _ _)  r@(Leaf _)       = Node (ct+1) l r
    join l@(Leaf _)       r@(Node ct _ _)  = Node (ct+1) l r
    join l@(Node ctl _ _) r@(Node ctr _ _) = Node (ctl+ctr) l r

{-
-- example:
Main> build_tree ['a','b','c','d','e']
Node 5 (Node 4 (Node 2 (Leaf 'a') (Leaf 'b'))
               (Node 2 (Leaf 'c') (Leaf 'd')))
       (Leaf 'e')

-}

-- given a non-empty sequence (e1,...en) to shuffle, and a sequence
-- (r1,...r[n-1]) of numbers such that r[i] is an independent sample
-- from a uniform random distribution [0..n-i], compute the
-- corresponding permutation of the input sequence.

shuffle1 :: [a] -> [Int] -> [a]
shuffle1 elements rseq = shuffle1' (build_tree elements) rseq
    where
    shuffle1' (Leaf e) [] = [e]
    shuffle1' tree (ri:r_others) = extract_tree ri tree 
                    (\tree -> shuffle1' tree r_others)
         -- extract_tree n tree
         -- extracts the n-th element from the tree and returns
         -- that element, paired with a tree with the element
         -- deleted (only instead of pairing, we use CPS)
         -- The function maintains the invariant of the completeness
         -- of the tree: all internal nodes are always full.
         -- The collection of patterns below is deliberately not complete.
         -- All the missing cases may not occur (and if they do,
         -- that's an error.
    extract_tree 0 (Node _ (Leaf e) r) k = e:k r
    extract_tree 1 (Node 2 l@Leaf{} (Leaf r)) k = r:k l
    extract_tree n (Node c l@Leaf{} r) k =
        extract_tree (n-1) r (\new_r -> k $ Node (c-1) l new_r)
    extract_tree n (Node n1 l (Leaf e)) k | n+1 == n1 = e:k l
                       
    extract_tree n (Node c l@(Node cl _ _) r) k
        | n < cl = extract_tree n l (\new_l -> k $ Node (c-1) new_l r)
        | otherwise = extract_tree (n-cl) r (\new_r -> k $ Node (c-1) l new_r)

-- -- Here the perfect shuffle algorithm taken from http://okmij.org/ftp/Haskell/perfect-shuffle.txt ends
-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 2 - EXERCISE 1 +++                                                      --

-- prettyPrint
--      This function given a lambda macro expression
--      pretty prints (unparses) it as a string. If a subexpression
--      in the lamda expression is syntactically equal to
--      one defined in a macro then it is replaced by the macro name.
--      Where two such subexpressions overlap, the larger of the two 
--      is rendered as a macro name. Where two macro names are defined to be 
--      the same expression, the one defined first in the term is used.
--      IMPORTANT: this function uses the minimum posssible
--                 number of parenthesis. Thus, it is may
--                 not be easily readable.
--      This function returns an error if not all macro names are uppercase.
--
prettyPrint :: LamMacroExpr -> String 

prettyPrint (LamDef xs e) | and $ map isUpperStringNotNull macros = ( concat $ map prettyPrintMacro unexpanded ) ++ ( prettyPrintLamExpr (map reversePair unexpanded) e )  -- all macro names must be uppercase
                          | otherwise = error "The macro names must be UPPERCASE"
                          where
                            unexpanded = unexpandMacros xs
                            isUpperStringNotNull [] = False  -- the empty list is null
                            isUpperStringNotNull ys = and $ map isUpper ys
                            (macros, express) = unzip xs
                            prettyPrintMacro = (\(a,b) -> "def " ++ a ++ " = " ++ (prettyPrintLamExpr [] b) ++ " in ")
                            reversePair = (\(a,b) -> (b,a))


-- unexpandMacros
--      This function unexpands macro definitions.
--
unexpandMacros :: [(String, LamExpr)] -> [(String, LamExpr)]

unexpandMacros xs = map reversePair (unexpandMacrosAux [] xs)
                  where
                    reversePair = (\(a,b) -> (b,a))
                    
                    -- This auxiliary function allows to unexpand macro definitions.
                    --
                    unexpandMacrosAux :: [(LamExpr,String)] -> [(String,LamExpr)] -> [(LamExpr,String)]
                    
                    unexpandMacrosAux ys [] = ys
                    unexpandMacrosAux ys ((a,b):xs) = unexpandMacrosAux (ys++ [(unexpandMacroGivenPrevious b, a)]) xs
                                                where
                                                
                                                 -- This auxiliary function unexpands a given macro definition
                                                 -- given the previously defined macros.
                                                 --
                                                  unexpandMacroGivenPrevious e@(LamVar _) = case lookup e ys of
                                                                                         Just x -> LamMacro x
                                                                                         Nothing -> e
                                                                                         
                                                  unexpandMacroGivenPrevious e@(LamMacro x) = case (lookup (LamMacro x) ys) of
                                                                                           Nothing -> e  -- no other macro name defines it
                                                                                           Just y -> case xPosition of  -- there exists a macro name 'y' which defines the macro name 'x'
                                                                                                        Nothing -> LamMacro y  -- if the macro name 'x' is not present then return the macro 'y'
                                                                                                        Just p -> if xPosition <= yPosition then LamMacro x else LamMacro y  -- if both of them are present then return the macro which appears first
                                                                                            where
                                                                                                macros = map snd ys
                                                                                                xPosition = lookup x (zip macros [1..])
                                                                                                yPosition = lookup y (zip macros [1..])
                                                                                        
                                                  unexpandMacroGivenPrevious (LamAbs n e) = case lookup (LamAbs n e) ys of
                                                                                         Just x -> LamMacro x
                                                                                         Nothing -> (LamAbs n (unexpandMacroGivenPrevious e))
                                                  
                                                  unexpandMacroGivenPrevious (LamApp e1 e2) = case lookup (LamApp e1 e2) ys of
                                                                                           Just x -> LamMacro x
                                                                                           Nothing -> LamApp (unexpandMacroGivenPrevious e1) (unexpandMacroGivenPrevious e2)


-- prettyPrintLamExpr
--      This function given a lambda expression pretty prints it
--      using the minimum possible number of parenthesis. Furthermore,
--      it takes as argument a lookup list  so that if a subexpression
--      in the lamda expression is syntactically equal to one defined in 
--      a macro then it is replaced by the macro name.
--      Where two such subexpressions overlap, the larger of the two 
--      is rendered as a macro name. Where two macro names are defined to be 
--      the same expression, the one defined first in the term is used.
--
prettyPrintLamExpr :: [(LamExpr,String)] -> LamExpr -> String

prettyPrintLamExpr [] (LamMacro x) = x  -- return the macro name
prettyPrintLamExpr xs (LamMacro x) = case (lookup (LamMacro x) xs) of
                                        Nothing -> x  -- no other macro name defines it
                                        Just y -> case xPosition of  -- there exists a macro name 'y' which defines the macro name 'x'
                                                     Nothing -> y  -- if the macro name 'x' is not present then return the macro name 'y'
                                                     Just p -> if xPosition <= yPosition then x else y  -- if both of them are present then return the macro name which appears first
                                            where
                                                macros = map snd xs
                                                xPosition = lookup x (zip macros [1..])
                                                yPosition = lookup y (zip macros [1..])                                               
                                                                                       
prettyPrintLamExpr [] (LamVar n) = "x"++(show n)
prettyPrintLamExpr xs (LamVar n) = case (lookup (LamVar n) xs) of
                                      Nothing -> "x"++ (show n)  -- there is no macro which defines this variable
                                      Just x -> x  -- there exists a macro  which defines this variable
                                        
-- if a lamda expression is a lambda application of two lambda expressions e1 and e2 where both e1 and e2 are lambda applications
-- as well then e1 must be pretty printed surrounded by parethesis and e2 follows suits (pretty printed e1) (pretty printed e2) only if the
-- right most (not lambda application and not LamApp _ (LamApp _ (LamAbs _ _))) lamda expression of e1 is a lamda abstraction . Otherwise, 
-- pretty printed e1 does not need to be surrounded by parenthesis. This follows because lamda applications associate to the left.  
--             
prettyPrintLamExpr [] (LamApp e1@(LamApp _ _) e2@(LamApp _ _) ) = case rightMost e1 of 
                                                                     LamAbs _ _ -> substWithPars e1' rightMostPrinted ++ " " ++ "(" ++ (prettyPrintLamExpr [] e2) ++ ")"  -- surround e1 with parenthesis if its rightMost (not lambda application) lamda expression is a lamda abstraction
                                                                     _ -> e1' ++  " " ++ "(" ++ (prettyPrintLamExpr [] e2) ++ ")"
                                                                where
                                                                    e1' = prettyPrintLamExpr [] e1
                                                                    rightMostPrinted = prettyPrintLamExpr [] (rightMost e1)
                                                                    
                                                                     
-- the same concepts as the previous pattern match but this time the lookup list is not empty
--
prettyPrintLamExpr xs (LamApp e1@(LamApp _ _) e2@(LamApp _ _) ) = case (lookup (LamApp e1 e2) xs) of
                                                                     Nothing -> case (isMacroe1', isMacroe2') of  -- there is no macro which defines this lambda expression
                                                                                   (True,True) -> e1' ++ " " ++ e2' -- both e1 and e2 are replaced by macro names
                                                                                   (True, False) -> e1' ++ " " ++ "(" ++ e2' ++ ")"  -- only e1 is replaced by a macro name
                                                                                   (False,True) -> case rightMost e1 of   -- only e2 is replaced by a macro name 
                                                                                                      LamAbs _ _ -> substWithPars e1' rightMostPrinted ++ " " ++ e2' -- surround e1 with parenthesis if its rightMost (not lambda applicationand and not LamApp _ (LamApp _ (LamAbs _ _)))
                                                                                                                                                                     -- lamda expression is a lamda abstraction
                                                                                                      _ ->  e1' ++ " " ++ e2'
                                                                                   (False,False) -> case rightMost e1 of   -- only e2 is replaced by a macro name 
                                                                                                       LamAbs _ _ -> substWithPars e1' rightMostPrinted ++ " " ++ "(" ++ e2' ++ ")" -- surround e1 with parenthesis if its rightMost (not lambda application and 
                                                                                                                                                                                    -- not LamApp _ (LamApp _ (LamAbs _ _))) lamda expression is a lamda abstraction
                                                                                                       _ -> e1' ++ " " ++ "(" ++ e2' ++ ")"
                                                                     Just x -> x  -- there exists a macro which defines this lambda expression
                                                                where
                                                                  e1' = prettyPrintLamExpr xs e1
                                                                  e2' = prettyPrintLamExpr xs e2
                                                                  isMacroe1' = and $ map isUpper e1'
                                                                  isMacroe2' = and $ map isUpper e2'
                                                                  rightMostPrinted = prettyPrintLamExpr xs (rightMost e1)

-- if a lambda expression is a lambda application of two lambda expressions e1 and e2 where e1 is a lambda application then if the 
-- first rightmost (not lambda application and not LamApp _ (LamApp _ (LamAbs _ _))) lamda expression of e1 is not a lamda abstraction then there is no need of surrounding pretty printed e1 with parenthesis.
-- However, if the rightmost lambda expression of e1 is a lamnda abstraction then pretty printed e1 must be surrouded by parenthesis because
-- lambda abstractions associate to the right.
--
prettyPrintLamExpr [] (LamApp e1@(LamApp _ _) e2 ) = case (rightMost e1) of
                                                        LamAbs _ _ -> substWithPars e1' rightMostPrinted ++ " " ++ (prettyPrintLamExpr [] e2)
                                                        _ -> (prettyPrintLamExpr [] e1) ++ " " ++ (prettyPrintLamExpr [] e2)
                                                   where
                                                     e1' = prettyPrintLamExpr [] e1
                                                     rightMostPrinted = prettyPrintLamExpr [] (rightMost e1)
                                                            
-- the same concepts as the previous similar match but this time the lookup list is not empty.
-- Consequently, if pretty printed e1 is a macro name then there is no need to surround it with parenthesis.
--
prettyPrintLamExpr xs (LamApp e1@(LamApp _ _) e2 ) = case (lookup (LamApp e1 e2) xs) of
                                                        Nothing -> if and $ map isUpper e1' then e1' ++ " " ++ (prettyPrintLamExpr xs e2) else case (rightMost e1) of
                                                                                                                                                  LamAbs _ _ -> substWithPars e1' rightMostPrinted ++ " " ++ (prettyPrintLamExpr xs e2)
                                                                                                                                                  _ -> e1' ++ " " ++ (prettyPrintLamExpr xs e2) 
                                                        Just x -> x  -- there exists a macro which defines this lambda expression
                                                   where
                                                     e1' = prettyPrintLamExpr xs e1
                                                     rightMostPrinted = prettyPrintLamExpr xs (rightMost e1)

-- if a lambda expression is a lambda application of two lambda expressions e1 and e2 where e1 is a lambda abstraction and e2 is a lambda 
-- application then both of them must be surrounded by parethesis because lambda abstractions associate to the right and lambda applications
-- to the left
--                                                        
prettyPrintLamExpr [] (LamApp e1@(LamAbs _ _) e2@(LamApp _ _) ) = "("++ (prettyPrintLamExpr [] e1) ++ ")"  ++ " " ++ "(" ++ (prettyPrintLamExpr [] e2) ++ ")"

-- the same concepts as the previous pattern match but this time the lookup list is not empty.          
--                                                   
prettyPrintLamExpr xs (LamApp e1@(LamAbs _ _) e2@(LamApp _ _)) = case (lookup (LamApp e1 e2) xs) of
                                                                    Nothing -> case (isMacroe1', isMacroe2') of  -- there is no macro which defines this lambda expression
                                                                                  (True,True) -> e1' ++ " " ++ e2'  -- both e1 and e2 are replaced by macro names
                                                                                  (True,False) ->  e1' ++ " " ++ "(" ++ e2' ++ ")"  -- only e1 is replaced by a macro name
                                                                                  (False,True) -> "(" ++ e1' ++ ")" ++ " " ++ e2'  -- only e2 is replaced by a macro name
                                                                                  (False,False) -> "(" ++ e1' ++ ")" ++ " " ++ "(" ++ e2' ++ ")"  -- none of them is replaced by a macro name
                                                                    Just x -> x  -- there exists a macro which defines this lambda expression
                                                              where
                                                                e1' = prettyPrintLamExpr xs e1
                                                                e2' = prettyPrintLamExpr xs e2
                                                                isMacroe1' = and $ map isUpper e1'
                                                                isMacroe2' = and $ map isUpper e2'

-- if a lambda expression is a lambda application of two lambda expressions e1 and e2 where e1 is neither a lambda application nor a lambda
-- abstraction then only pretty printed e2 must be surrounded with parenthesis.
--
prettyPrintLamExpr [] (LamApp e1 e2@(LamApp _ _) ) = (prettyPrintLamExpr [] e1)  ++ " " ++ "(" ++ (prettyPrintLamExpr [] e2) ++ ")"

-- the same concepts as the previous pattern match but this time the lookup list is not empty.          
--                                                             
prettyPrintLamExpr xs (LamApp e1 e2@(LamApp _ _) ) = case (lookup (LamApp e1 e2) xs) of
                                                        Nothing -> if and $ map isUpper e2' then (prettyPrintLamExpr xs e1)  ++ " " ++ e2' else (prettyPrintLamExpr xs e1)  ++ " " ++ "(" ++ e2' ++ ")"  -- if pretty printed e2 is a macro name then there is no need of surrounding it with parethesis
                                                        Just x -> x  -- there exists a macro which defines this lambda expression
                                                   where
                                                     e2' = prettyPrintLamExpr xs e2

-- if a lambda expression is a lambda application of two lamnda expressions e1 and e2 where e1 is a lambda abstraction and e2 is not
-- a lambda application then only pretty printed e1 must be surrounded with parenthesis.
--
prettyPrintLamExpr [] (LamApp e1@(LamAbs _ _) e2) = "(" ++ (prettyPrintLamExpr [] e1) ++ ")" ++ " " ++ (prettyPrintLamExpr [] e2) 

-- the same concepts as the previous pattern match but this time the lookup list is not empty.          
--                                                           
prettyPrintLamExpr xs (LamApp e1@(LamAbs _ _) e2) = case (lookup (LamApp e1 e2) xs) of
                                                       Nothing -> if and $ map isUpper e1' then e1' ++ " " ++ (prettyPrintLamExpr xs e2) else "(" ++ e1' ++ ")" ++ " " ++ (prettyPrintLamExpr xs e2)  -- if pretty printed e1 is a macro name then there is no need of surrounding it with parethesis
                                                       Just x -> x  -- there exists a macro which defines this lambda expression
                                                       where
                                                         e1' = prettyPrintLamExpr xs e1

-- if a lambda expression is a lambda application of two lamnda expressions e1 and e2 where e1 is neither a lambda application nor
-- a lambda abstraction and e2 is not a lamnda application then both pretty printed e1 and pretty printed e2 do not need to be
-- surrounded by parenthesis.
-- 
prettyPrintLamExpr [] (LamApp e1 e2) = (prettyPrintLamExpr [] e1) ++ " " ++ (prettyPrintLamExpr [] e2)
                                                                                                                                    
-- the same concepts as the previous pattern match but this time the lookup list is not empty.          
--                                                              
prettyPrintLamExpr xs (LamApp e1 e2) = case (lookup (LamApp e1 e2) xs) of
                                          Nothing -> (prettyPrintLamExpr xs e1) ++ " " ++ (prettyPrintLamExpr xs e2)
                                          Just x -> x  -- there exists a macro which defines this lambda expression
                                                                            
                                                                            
prettyPrintLamExpr [] (LamAbs n e) = "\\x" ++(show n) ++ " -> " ++ (prettyPrintLamExpr [] e)
prettyPrintLamExpr xs (LamAbs n e) = case (lookup (LamAbs n e) xs) of
                                        Just x -> x  -- there exists a macro which defines this lambda expression
                                        Nothing -> "\\x" ++ (show n) ++ " -> " ++ (prettyPrintLamExpr xs e)
       
       
-- rightMost
--      This function returns the first rightmost lambda expression,
--      which is not a lambda application, given a provided lambda expression.
--          %%EXAMPLE 1:
--                  rightMost (LamApp (LamVar 1) (LamApp (LamVar 2) (LamMacro "M"))) = LamMacro "M"
--          %%EXAMPLE 2:
--                  rightMost (LamApp (LamVar 1) (LamAbs 1 (LamVar 1))) = LamAbs 1 (LamVar 1)
--          %%EXAMPLE 2:
--                  rightMost (Lamvar 1) = LamVar 1
--
rightMost :: LamExpr -> LamExpr

rightMost e@(LamAbs _ _) = e
rightMost e@(LamVar _) = e
rightMost e@(LamMacro _) = e
rightMost e@(LamApp _ (LamApp _ (LamAbs _ _))) = e
rightMost e@(LamApp e1 e2) = rightMost e2


-- substWithPars
--      This function takes two strings representing a different lambda
--      expression. It is assumed that the second string argument's reverse is a 
--      prefix of the reverse of the first argument string.
--      It returns the first argument string with an added set of parenthesis that surround
--      its ending sublist that matches the second argument string.
--
substWithPars :: String -> String -> String

substWithPars  xs ys = (take (length xs - length ys) xs) ++ "(" ++ ys ++ ")"
                     where
                        leng = zip (reverse xs) ys

                    
-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 2 - EXERCISE 2 +++                                                      --

-- parseLamMacro
--      This function parses a lambda expression with macros
--      using the following concrete syntax:
--                                          MacroExpr ::= "def" MacroName "=" Expr "in" MacroExpr | Expr
--                                          Expr ::= Var | MacroName | Expr Expr | “\” Var “->” Expr | “(“ Expr “)”
--                                          MacroName ::= UChar | UChar MacroName
--                                          UChar ::= "A" | "B" | ... | "Z"
--                                          Var ::= “x” Digits
--                                          Digits ::= Digit | Digit Digits
--                                          Digit ::= “0” | “1” | “2” | “3” | “4” | “5” | “6” | “7” | “8” | “9”
--
--      This  function returns Nothing if the given string does not parse correctly according to the rules of the
--      grammar. Additionally, it returns Nothing if macros are not uniquely defined or contain free terms.
--      Otherwise, a valid Abstract Syntax Tree is returned.
--
parseLamMacro :: String -> Maybe LamMacroExpr

parseLamMacro [] = Nothing
parseLamMacro xs = case parse macroExpr xs of
                      [] -> Nothing  -- the given string does not parse correctly
                      [(a,ys)] -> case filteredys of
                                     "" -> Just a  -- if 'filteredys' is an empty string then the leftover string 'ys' is an empty string 
                                                   -- or a string containing only spaces thus the parsing is successful
                                                   
                                     (x:xs) -> Nothing  -- the parsing is not successful because  the leftover string 'ys' is a string which 
                                                        -- cannot be parsed according to the rules of the grammar
                       where
                         filteredys = filter (\x -> not (isSpace x)) ys  --removes all spaces in the leftover string produced after parsing the string xs
                        
                        
-- macroExpr
--      This function is a parser for lambda macro expressions.
--      The concrete syntax that it uses is described in the 
--      function 'parseLamMacro'.
--
macroExpr :: Parser LamMacroExpr

macroExpr = do
              e1 <- some macroExprAuxiliary  -- parse all the Macro definitions storing them into tuples (MacroName,Expr)
              let (macros,express) = unzip e1
              if ((length . nub) macros /= length macros) || (not $ (and . map isClosed) express) then  -- if there are macro name duplicates or macros contain 
                                                                                                        -- free terms then the parsing is not successful
                empty -- returns []
              else
                  do
                    e2 <- expr  -- parse a lambda expression
                    (return (LamDef e1 e2))
             <|>  --if Macro definitions are not present
                do
                  e <- expr  -- parse a lambda expression
                  return (LamDef [] e)
         where
           -- Let "def" MacroName "=" Expr "in" be called Macro definition
           -- This function parses a Macro definition
           macroExprAuxiliary :: Parser (String,LamExpr)
           macroExprAuxiliary = do
                                  space
                                  string "def"
                                  space
                                  macroName <- some upper
                                  space
                                  char '='
                                  space
                                  e <- expr
                                  space
                                  string "in"
                                  return (macroName,e)
                                        
                            
-- expr
--      This function is a parser for lambda expressions.
--      The concrete syntax that it uses is described in the 
--      function 'parseLamMacro'.
--                         
expr :: Parser LamExpr

expr =  do
          e <- some exprAuxiliary 
          if e == [] then  -- it does not parses correctly
            empty
          else
            if length e == 1 then  -- the parsed expression does not contain lambda applications except those inside e
              return (head e)
            else
              return (foldl1 (LamApp) e)  -- this fold allows to respect the left-associativity of the lambda applications
     where
       -- This function parses a lambda expression surrounded by parethesis or lambda variable or a macro variable or a lambda abstraction
       exprAuxiliary :: Parser LamExpr
       exprAuxiliary = do
                         space
                         char '('
                         space
                         e <- expr  -- this call allows to treat all the elements within the parenthesis as a single Abstract Syntax Tree.
                                    -- Thus, maintaining the precedence dictated by the parenthesis.
                         space
                         char ')'
                         return e
                         <|> variable <|> macroVariable <|> lambdaAbstraction

                                       
-- lambdaAbstraction
--      This function is a parser for a lambda abstraction.
--      The concrete syntax that it uses is described in the 
--      function 'parseLamMacro'.
--
lambdaAbstraction :: Parser LamExpr

lambdaAbstraction = do
                      space
                      char '\\'    
                      var <- variable
                      space
                      string "->"
                      space
                      e <- expr
                      return (LamAbs (extractNum var) e )


-- macroVariable
--      This function is a parser for a macro variable.
--      The concrete syntax that it uses is described in the 
--      function 'parseLamMacro'.
--                      
macroVariable :: Parser LamExpr

macroVariable = do
                  space
                  name <- some upper
                  return (LamMacro name) 


-- variable
--      This function is a parser for a lambda variable.
--      The concrete syntax that it uses is described in the 
--      function 'parseLamMacro'.
--             
variable :: Parser LamExpr

variable = do
             space
             char 'x'
             number <- nat
             return (LamVar number)
    
    
-- extractNum
--      This function extracts the variable number
--      of a lambda variable.
--
extractNum :: LamExpr -> Int

extractNum (LamVar x) = x
extractNum _ = error "This function works only with LamVar"

                              
-- isClosed
--      This function checks whether a lambda expression
--      is a closed term.
-- 
isClosed :: LamExpr -> Bool

isClosed e = and $ map (\x -> not (freeVar x e)) allVars
           where
             allVars = allVariables e  -- all variables in the lambda expression


-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 3 - EXERCISE 1 +++                                                      --

-- cpsTransform
--      This function translates a lambda macro expression into one
--      in continuation-passing style. Free variables are not captured.
--
cpsTransform :: LamMacroExpr -> LamMacroExpr

cpsTransform (LamDef ns e) = LamDef (map macroToCps ns) (tocpsLamExpr [1..] e)
                           where
                             macroToCps = (\(a,b)-> (a,tocpsLamExpr [1..] b))


-- tocpsLamExpr
--      This funcion translates a lambda expression into one
--      in continuation-passing style. Since, variables are added
--      when transforming into continuation-passing style, the first
--      argument must be provided so that to indicate which variable
--      numbers can be inserted into the lambda expression in
--      continuation style. It is important to notice that the choice
--      of these numbers is up to the user according to his preference
--      as the function then will use only the ones not already present in 
--      the provided lambda expression so that to avoid free variables capturing.
--      IMPORTANT: It is strongly suggested to use an infinite list of 
--                 variable numbers.
--   
tocpsLamExpr :: [Int] -> LamExpr -> LamExpr

tocpsLamExpr ns e = tocpsLamExprAuxiliary (ns \\ (allVariables e)) e  -- the auxiliary function is called with a list of variable numbers 
                                                                      -- so that none of them appears in the provided lambda expression
                  where
                    -- this auxilairy function just implements the functionality of 'tocpslamExpr'
                    tocpsLamExprAuxiliary :: [Int] -> LamExpr -> LamExpr
                    
                    tocpsLamExprAuxiliary (k:ns) (LamVar n) = LamAbs k (LamApp (LamVar k) (LamVar n))  -- < x > = λκ.(κ x)
                                                            
                    tocpsLamExprAuxiliary  _ (LamMacro xs) = LamMacro xs  -- < X > = X
                    
                    tocpsLamExprAuxiliary (k:ns) (LamAbs n e) = LamAbs k (LamApp (LamVar k) (LamAbs n (tocpsLamExprAuxiliary ns e)))  -- < λx.E > = λκ.(κ λx. < E >)
                                                              
                    tocpsLamExprAuxiliary (k:f:e:ns) (LamApp e1 e2) = LamAbs k (LamApp e1' (LamAbs f (LamApp (e2') (LamAbs e (LamApp (LamApp (LamVar f) (LamVar e))(LamVar k))))))  -- < (E1 E2) > = λκ.( < E1 > λf.(< E2 > λe.(f e κ)))
                                                                    where
                                                                      e1' = tocpsLamExprAuxiliary ns e1
                                                                      e2' = tocpsLamExprAuxiliary (ns \\ (allVariables e1'))  e2
     
     
-- cpsUntransform
--      This function translates a lambda macro expression in
--      continuation-passing style into a standard lambda
--      macro expression.
-- 
cpsUntransform :: LamMacroExpr -> LamMacroExpr

cpsUntransform (LamDef xs e) = LamDef (map macroFromCps xs) (fromcpsLamExpr e)
                             where
                               macroFromCps = (\(a,b) -> (a, fromcpsLamExpr b))


-- fromcpsLamExpr
--      This function translates a lambda expression in
--      continuation-passing style into a standard lamda
--      expression. If the given lambda expression is not
--      in continuation-passing style then an error will
--      occur.
--
fromcpsLamExpr :: LamExpr -> LamExpr

fromcpsLamExpr (LamMacro x) = LamMacro x

fromcpsLamExpr (LamAbs n (LamApp (LamVar n1) (LamVar n2))) | n == n1 = LamVar n2
                                                           | otherwise = error "Not in CPS"
                                                           
fromcpsLamExpr (LamAbs n1 (LamApp (LamVar n2) (LamAbs n3 e))) | n1 == n2 = LamAbs n3 (fromcpsLamExpr  e)
                                                              | otherwise = error "Not in CPS"
                                                              
fromcpsLamExpr (LamAbs n1 (LamApp e1 (LamAbs n2 (LamApp e2 (LamAbs n3 (LamApp (LamApp (LamVar n4) (LamVar n5 )) (LamVar n6))))))) | n1==n6 && n2==n4 && n3==n5 = LamApp (fromcpsLamExpr e1) (fromcpsLamExpr e2 )
                                                                                                                                  | otherwise = error "Not in CPS"
                                                                                                                                  
                                                                                                                                  
-- allVariables
--      This function returns all the variable numbers
--      contained in a given lambda expression.
--
allVariables :: LamExpr -> [Int]

allVariables (LamMacro xs) = []
allVariables (LamVar n) = [n]
allVariables (LamAbs n e) =  [n] ++ (allVariables e) 
allVariables (LamApp e1 e2) = (allVariables e1) ++ (allVariables e2)


-- allMacros
--      This function returns all the macro names
--      contained in a given lambda expression.
allMacros :: LamExpr -> [String]

allMacros (LamMacro xs) = [xs]
allMacros (LamVar _) = []
allMacros (LamAbs _ e) = allMacros e
allMacros (LamApp e1 e2) = (allMacros e1) ++ (allMacros e2)

-------------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------------
--                                                            +++ TASK 3 - EXERCISE 2 +++                                                      --

-- compareInnerOuter
--      This function takes a lambda macro expression and a positive integer bound and returns a 4-tuple
--      containing the length of different reduction sequences up to the provided bound. If a reduction 
--      does not terminate within the given bound (i.e. the number of reduction steps is strictly greater than the bound)
--      then Nothing is returned. Given an input expression E, the 4-tuple contains lengths for:
--          1. Innermost reduction on E
--          2. Outermost reduction on E
--          3. Innermost reduction on the CPS translation of E applied to the identity: < E > (λx -> x)
--          4. Outermost reduction on the CPS translation of E applied to the identity: < E> (λx -> x)
--
compareInnerOuter :: LamMacroExpr -> Int -> ( Maybe Int, Maybe Int, Maybe Int, Maybe Int )

compareInnerOuter e n | n < 0 = error "The argument cannot be less than 0"
                      | otherwise = ((numberSteps innerRedn1 e n),(numberSteps outerRedn1 e n), (numberSteps innerRedn1 eCps n), (numberSteps outerRedn1 eCps n))
                      where
                        LamDef xs e' = cpsTransform e
                        id = (LamAbs 1 (LamVar 1))
                        eCps = (LamDef xs (LamApp e' id))
                        
                        
-- numberSteps
--      This function takes as argument a one-step evaluation function,
--      a lambda macro expression and an integer number. It returns the number
--      of steps that it takes for the provided lambda macro expression to be fully
--      reduced (no redexes present) by using the provided one-step evalutation function.
--      If it is not possible to fully reduce the provided lambda macro expression within
--      a number of steps less than or equal to the provided integer number then Nothing
--      is returned.
-- 
numberSteps :: (LamMacroExpr -> Maybe LamMacroExpr) -> LamMacroExpr -> Int -> Maybe Int

numberSteps f e n = elemIndex Nothing firstNSteps
                  where
                    evals = evalSteps f e
                    firstNSteps = (take (n+1) . tail) evals


-- evalSteps
--      This function takes as argument a one-step evaluation function
--      and a lambda macro expression. It returns an infinite list of
--      lambda expressions such that the subsequent lambda expression e2
--      of a lambda expression e1 is the result of applying the one-step
--      evaluation function to e1. The previous lambda expression of the 
--      first occurrence of Nothing is a non-reducible lambda expression.
--                             
evalSteps :: (LamMacroExpr -> Maybe LamMacroExpr) -> LamMacroExpr -> [Maybe LamMacroExpr]

evalSteps f e = iterate (\x -> x >>= f) (return e)


-- outerRedn1
--      This function takes a lambda expression with macros
--      and performs a single reduction on that expression 
--      using leftmost outermost evaluation. If Nothing is
--      returned then the given lambda expression cannot be
--      reduced (it containes no redexes).
-- 
outerRedn1 :: LamMacroExpr -> Maybe LamMacroExpr

-- if there is at least one macro definition then the outermost reduction is the expansion of the leftmost macro definition
outerRedn1 (LamDef ((ms,e1):xs) e2) = Just (LamDef xs' (substMacro e2 ms e1))  -- macro expansion
                                    where
                                      xs' = map (\(a,b) -> (a, substMacro b ms e1)) xs  -- the macro expansion implies that def X = E in ME ----> ME [ E / X ] 
                                                                                        -- in which all occurrences of X in ME are replaced by their corresponding definition

outerRedn1 (LamDef [] e) = case outerRedn1Aux e of
                              Left e' -> Nothing  -- the lambda expression is not reducible
                              Right e' -> Just (LamDef [] e')  -- the lambda expression is reduced successfully
                         where
                           -- this auxiliary function returns (Left expression) if the provided
                           -- expression cannot be reduced. It returns (Right expression) if the
                           -- provided expression contains a redex and so it has been reduced.
                           --
                           outerRedn1Aux :: LamExpr -> Either LamExpr LamExpr
                                
                           outerRedn1Aux (LamVar n) = Left (LamVar n)  -- no reduction occurs
                           outerRedn1Aux (LamMacro xs) = Left (LamMacro xs)  -- no reduction occurs
                                
                           outerRedn1Aux (LamAbs n e) = case outerRedn1Aux e of
                                                           Left e' -> Left (LamAbs n e')  -- no reduction occurs
                                                           Right e' -> Right (LamAbs n e')  -- a reduction occurs
                                                                
                           outerRedn1Aux (LamApp (LamAbs n e1) e2) = Right (substVar e1 n e2)  -- a reduction occurs
                                
                           outerRedn1Aux (LamApp e1 e2) = case outerRedn1Aux e1 of
                                                             Left e1' -> case outerRedn1Aux e2 of  -- if  no reduction occurs on the left (the left expression e1 is 
                                                                                                  -- tried first as leftmost outermost evaluation is used), try with e2
                                                             
                                                                            Left e2' -> Left (LamApp e1' e2')  -- no reduction occurs in e2
                                                                            Right e2' -> Right (LamApp e1' e2')  --  a reduction occurs in e2
                                                             Right e1' -> Right (LamApp e1' e2)  -- a reduction occurs in e1
                                                                    
                                                                    
-- innerRedn1
--      This function takes a lambda expression with macros
--      and performs a single reduction on that expression 
--      using leftmost innermost evaluation. If Nothing is
--      returned then the given lambda expression cannot be
--      reduced (it containes no redexes).
--                                                                   
innerRedn1 :: LamMacroExpr -> Maybe LamMacroExpr

innerRedn1 (LamDef xs e) = case innerRedn1Aux e of
                              Left e' -> if xs == [] then Nothing else Just (LamDef (take ((length xs)-1) xs) (substMacro e lastMacro expr))  -- if no reduction occurs in 'e' and there is no macro definition left then no reduction can occur.
                                                                                                                                              -- Otherwise, the innermost reduction is the expansion of the rightmost macro definition
                              Right e' -> Just (LamDef xs e')  -- a reduction occurs
                        where
                          (lastMacro,expr) = (head . reverse) xs
                                
                          -- this auxiliary function returns (Left expression) if the provided
                          -- expression cannot be reduced. It returns (Right expression) if the
                          -- provided expression contains a redex and so it has been reduced.
                          --
                          innerRedn1Aux :: LamExpr -> Either LamExpr LamExpr
                                
                          innerRedn1Aux (LamVar n) = Left (LamVar n)  -- no reduction occurs
                          innerRedn1Aux (LamMacro xs) = Left (LamMacro xs)  -- no reduction occurs
                                
                          innerRedn1Aux (LamAbs n e) = case innerRedn1Aux e of
                                                          Left e' -> Left (LamAbs n e')  -- no reduction occurs
                                                          Right e' -> Right (LamAbs n e')  -- a reduction occurs
                                                                
                          innerRedn1Aux (LamApp (LamAbs n e1) e2) = case innerRedn1Aux e1 of
                                                                       Left e1' -> case innerRedn1Aux e2 of  -- no reduction occurs in e1
                                                                                      Left e2' -> Right (substVar e1 n e2)  -- if no reduction occurs in e2 then this redex is the left innermost one. It can be reduced
                                                                                      Right e2' -> Right (LamApp (LamAbs n e1') e2')  -- a reduction occurs in e2
                                                                       Right e1' -> Right (LamApp (LamAbs n e1') e2)  -- a reduction occurs in e1
                                                                            
                          innerRedn1Aux (LamApp e1 e2) = case innerRedn1Aux e1 of
                                                            Left e1' -> case innerRedn1Aux e2 of  -- no reduction occurs in e1
                                                                           Left e2' -> Left (LamApp e1' e2')  -- no reduction occurs in e2
                                                                           Right e2' -> Right (LamApp e1' e2')  -- a reduction occurs in e2
                                                            Right e1' -> Right (LamApp e1' e2)  -- a reduction occurs in e1             
                                      
                                      
-- substMacro
--      This function takes as argument a lambda expression e,
--      a string x and another lamnda expression e2 so that to
--      return a lambda expression where all the occurrences of
--      the macro x in e are replaced by e2.
--                                       
substMacro :: LamExpr -> String -> LamExpr -> LamExpr

substMacro (LamMacro xs) ys e2 | xs == ys = e2
                               | otherwise = LamMacro xs 
                               
substMacro (LamVar n) _ _ = LamVar n
substMacro (LamAbs n e1) ys e2 = LamAbs n (substMacro e1 ys e2)
substMacro (LamApp e1 e2) ys e3 = LamApp (substMacro e1 ys e3) (substMacro e2 ys e3)

-- substVar
--      This function takes as argument a lambda expression e,
--      an integer n and another lamda expression e2 so that to return
--      a lambda expression where all the occurrences of the variable n
--      in e are replaced by e2.
--
substVar :: LamExpr -> Int -> LamExpr -> LamExpr

substVar (LamVar n1) n2 e | n1 == n2 = e
                          | otherwise = LamVar n1
                          
substVar (LamMacro ps) _ _ = LamMacro ps 
substVar (LamApp e1 e2) n2 e = LamApp (substVar e1 n2 e) (substVar e2 n2 e)

substVar (LamAbs n1 e1) n2 e | n1 /= n2 && not (freeVar n1 e) = LamAbs n1 (substVar e1 n2 e)
                             | n1 /=n2 && (freeVar n1 e) = let n1' = (renameVar n1 e1) in substVar (LamAbs n1' (substVar e1 n1 (LamVar n1'))) n2 e
                             | n1 == n2 = LamAbs n1 e1
                             
-- freeVar
--      This function checks whether a given variable
--      is free in a given lamda expression.
--
freeVar :: Int -> LamExpr -> Bool

freeVar n1 (LamVar n2) = n1 == n2
freeVar n1 (LamMacro _) = False

freeVar n1 (LamAbs n2 e) | n1 == n2 = False
                         | otherwise = freeVar n1 e
                         
freeVar n1 (LamApp e1 e2) = freeVar n1 e1 || freeVar n1 e2

-- renameVar
--      This function renames a given variable such that
--      the new variable number is not free in the given
--      expression.
--
renameVar :: Int -> LamExpr -> Int

renameVar n e | freeVar (n+1) e = renameVar (n+1) e
              | otherwise = (n+1) 