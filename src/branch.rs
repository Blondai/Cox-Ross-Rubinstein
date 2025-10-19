//! This module contains all the implementations of everything branch related.

use crate::Tick::{Down, Up};
use std::fmt;

/// A struct representing a branch of the binomial tree.
///
/// The information of [`Up`] and [`Down`] movements is elegantly stored in a `u128`.
/// To speed up computations the number of [`Up`] and [`Down`] movements is also stored here.
#[derive(Debug, Copy, Clone)]
pub struct Branch {
    /// The binary representation will correspond to the [`Branch`].
    ///
    /// A `1` will mean an [`Up`] movement and a `0` a [`Down`] movement.
    ticks: u128,

    /// The length of the [`Branch`].
    ///
    /// Maximum supported length is 128 as the [`Branch`] ist stored in an `u128`.
    length: usize,

    /// The amount of up movements.
    ///
    /// This is the amount of ones in the `u128`.
    ups: usize,

    /// The amount of down movements.
    ///
    /// This is the length of the branch minus the amount of up movements.
    /// We can not count the amount of zeros as the length will most likely not be 128.
    downs: usize,
}

impl Branch {
    /// Creates a new [`Branch`] instance.
    ///
    /// # Arguments
    ///
    /// * `ticks`: The u128 representing the [`Up`] and [`Down`] movements.
    /// A `1` will mean an [`Up`] movement and a `0` a [`Down`] movement.
    /// * `length`: The length up to which point the zeros in `ticks` should be counted as [`Down`].
    ///
    /// # Returns
    ///
    /// * [`BranchError::TooLarge`]: The length is bigger than 128.
    /// * [`BranchError::BitBeyondLength`]: A 1 is beyond the bit at position 128.
    /// * [`Branch`]: Other wise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// // (Up, Up, Down)
    /// let branch: Branch = Branch::new(3_u128, 3).unwrap();
    /// assert_eq!(branch.to_ticks()[0], Tick::Up);
    /// assert_eq!(branch.to_ticks()[1], Tick::Up);
    /// assert_eq!(branch.to_ticks()[2], Tick::Down);
    /// // Too Large
    /// let too_large: BranchError = Branch::new(3_u128, 256).err().unwrap();
    /// assert_eq!(too_large, BranchError::TooLarge { length: 256 });
    /// // Bit beyond length
    /// let bit_beyond_length: BranchError = Branch::new(3_u128, 1).err().unwrap();
    /// assert_eq!(bit_beyond_length, BranchError::BitBeyondLength { number: 3, length: 1 });
    /// ```
    #[inline]
    pub fn new(ticks: u128, length: usize) -> Result<Self, BranchError> {
        BranchError::check_length(length)?;
        BranchError::check_bits(ticks, length)?;

        let ups: usize = ticks.count_ones() as usize; // Max 128
        let downs: usize = length - ups; // Max 128

        Ok(Self {
            ticks,
            length,
            ups,
            downs,
        })
    }

    /// Creates a new [`Branch`] without any checks.
    ///
    /// This should be used internally only.
    #[inline]
    pub(crate) fn new_unchecked(ticks: u128, length: usize) -> Branch {
        let ups: usize = ticks.count_ones() as usize;
        let downs: usize = length - ups;

        Self {
            ticks,
            length,
            ups,
            downs,
        }
    }

    /// Returns the length of a [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// assert_eq!(branch.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns the number of [`Up`] movements of a [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// assert_eq!(branch.ups(), 2);
    /// ```
    #[inline]
    pub fn ups(&self) -> usize {
        self.ups
    }

    /// Returns the number of [`Down`] movements of a [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// assert_eq!(branch.downs(), 1);
    /// ```
    #[inline]
    pub fn downs(&self) -> usize {
        self.downs
    }

    /// Creates a new [`Branch`] instance based on a slice of [`Tick`]s.
    ///
    /// # Arguments
    ///
    /// * `ticks`: A slice of [`Up`] and [`Down`] movements.
    ///
    ///  # Returns
    ///
    /// * [`BranchError::TooLarge`]: The length of the slice is larger than 128.
    /// * [`Branch`]: Other wise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// assert_eq!(branch.to_ticks()[0], Tick::Up);
    /// assert_eq!(branch.to_ticks()[1], Tick::Up);
    /// assert_eq!(branch.to_ticks()[2], Tick::Down);
    /// // Too large
    /// let ticks: [Tick; 256] = [Tick::Down; 256];
    /// let too_large: BranchError = Branch::from_ticks(&ticks).err().unwrap();
    /// assert_eq!(too_large, BranchError::TooLarge { length: 256 });
    /// ```
    pub fn from_ticks(ticks: &[Tick]) -> Result<Self, BranchError> {
        BranchError::check_length(ticks.len())?;

        let mut number: u128 = 0;

        for (index, &tick) in ticks.iter().enumerate() {
            if tick == Up {
                // Bit at index to 1
                number |= 1 << index;
            }
            // Down nothing bit already 0
        }
        Ok(Self::new_unchecked(number, ticks.len()))
    }

    /// Returns the [`Tick`] representation of a [`Branch`].
    ///
    /// This will create a vector of [`Up`] and [`Down`] movements based on the [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// assert_eq!(branch.to_ticks()[0], Tick::Up);
    /// assert_eq!(branch.to_ticks()[1], Tick::Up);
    /// assert_eq!(branch.to_ticks()[2], Tick::Down);
    /// ```
    pub fn to_ticks(&self) -> Vec<Tick> {
        let mut ticks: Vec<Tick> = Vec::with_capacity(self.length);

        for index in 0_usize..self.length {
            if (self.ticks >> index) & 1_u128 == 1_u128 {
                ticks.push(Up);
            } else {
                ticks.push(Down);
            }
        }

        ticks
    }

    /// Creates a new [`Branch`] based on the [`Branch`] with the [`Tick`] added.
    ///
    /// # Returns
    ///
    /// * [`BranchError::TooLarge`]: The inital length was already 128.
    /// * [`Branch`]: Other wise.
    ///
    ///
    /// # Example
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// let new_branch: Branch = branch.add(Tick::Up).unwrap();
    /// assert_eq!(new_branch.to_ticks()[0], Tick::Up);
    /// assert_eq!(new_branch.to_ticks()[1], Tick::Up);
    /// assert_eq!(new_branch.to_ticks()[2], Tick::Down);
    /// assert_eq!(new_branch.to_ticks()[3], Tick::Up);
    /// ```
    #[inline]
    pub fn add(&self, tick: Tick) -> Result<Self, BranchError> {
        let mut ticks: u128 = self.ticks;
        let length: usize = self.length + 1;

        BranchError::check_length(length)?;

        if tick == Up {
            ticks |= 1 << self.length
        }

        Ok(Self::new_unchecked(ticks, length))
    }

    /// Creates a new [`Branch`] without any checks by adding a [`Up`]- or [`Down`]-Tick.
    ///
    /// This should be used internally only.
    pub(crate) fn add_unchecked(&self, tick: Tick) -> Self {
        let mut ticks: u128 = self.ticks;
        let length: usize = self.length + 1;

        if tick == Up {
            ticks |= 1 << self.length
        }

        Self::new_unchecked(ticks, length)
    }

    /// Creates a [`BranchIter`] from a [`Branch`].
    ///
    /// This allows the user to iterate through the [`Tick`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchError, Tick};
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Up];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// for tick in branch.iter() {
    ///     assert_eq!(tick, Tick::Up);
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> BranchIter {
        BranchIter::new(self)
    }
}

impl PartialEq for Branch {
    /// Compars two [`Branch`] instances.
    ///
    /// They are equal if they have the same `ticks` and the same `length`.
    fn eq(&self, other: &Self) -> bool {
        self.ticks == other.ticks && self.length == other.length
    }
}

impl fmt::Display for Branch {
    /// Formats a [`Branch`] instances based on its representation in [`Tick`]s.
    ///
    /// This uses the [`Branch::to_ticks`] method.
    fn fmt(&self, format: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(format, "{:?}", self.to_ticks())
    }
}

/// The possible movements in the model.
///
/// They are mostly for readability.
/// The underlying calculations run on a `u128`, where `1` means [`Up`] and `0` means [`Down`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tick {
    /// Up movement.
    ///
    /// Internally `1`.
    Up,

    /// Down movement.
    ///
    /// Internally `0`.
    Down,
}

/// A struct for handling the iteration over a [`Branch`].
#[derive(Debug, Clone, Copy)]
pub struct BranchIter {
    branch: Branch,
    index: usize,
}

impl BranchIter {
    /// Creates a new [`BranchIter`] instance.
    ///
    /// This copies the underlying [`Branch`] and sets the `index` to zero.
    pub fn new(branch: &Branch) -> Self {
        Self {
            branch: *branch, // Cheap copy
            index: 0,
        }
    }
}

impl Iterator for BranchIter {
    type Item = Tick;

    /// Returns the bit at the current position of `index` in the [`Branch`]es binary representation.
    fn next(&mut self) -> Option<Self::Item> {
        // End
        if self.index >= self.branch.len() {
            return None;
        }

        // Bit at current index
        let tick = if (self.branch.ticks >> self.index) & 1 == 1 {
            Up
        } else {
            Down
        };

        self.index += 1;

        Some(tick)
    }
}

/// A struct for iterating over all possible [`Branch`]es of a model of a specific `length`.
///
/// # Notes
///
/// A model of length `n` will have `2^n` different [`Branch`]es.
/// This is exponential growth!
#[derive(Debug, Copy, Clone)]
pub struct BranchGenerator {
    current_tick: Option<u128>,
    length: usize,
    end_tick: u128,
}

impl BranchGenerator {
    /// Creates a new [`BranchGenerator`] instance.
    ///
    /// This should probably be used mostly internally.
    ///
    /// # Notes
    ///
    /// The [`Branch`]es are generated by repeatedly adding `1` to a `u128` starting at `0`.
    /// This will automatically end when reaching `2^length` as this is the [`Branch`] with all ones.
    ///
    /// # Arguments
    ///
    /// * `length`: The length of the model.
    ///
    /// # Returns
    ///
    /// * [`BranchError::TooLarge`]: When the `length` is larger than 128.
    /// * [`BranchGenerator`]: Other wise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, BranchGenerator, Tick};
    /// let mut generator: BranchGenerator = BranchGenerator::new(1).unwrap();
    /// assert_eq!(generator.next(), Branch::from_ticks(&[Tick::Down]).ok());
    /// assert_eq!(generator.next(), Branch::from_ticks(&[Tick::Up]).ok());
    /// assert_eq!(generator.next(), None);
    /// ```
    pub fn new(length: usize) -> Result<Self, BranchError> {
        BranchError::check_length(length)?;

        // 2^length or 0 for 2^128
        let end_tick: u128 = 1_u128.checked_shl(length as u32).unwrap_or(0);

        Ok(Self {
            current_tick: Some(0_u128),
            length,
            end_tick,
        })
    }
}

impl Iterator for BranchGenerator {
    type Item = Branch;

    /// Yields the next [`Branch`] in the [`BranchGenerator`].
    ///
    /// The [`Branch`]es are generated by repeatedly adding `1` to a `u128` starting at `0`.
    /// This will automatically end when reaching `2^length` as this is the [`Branch`] with all ones.
    ///
    /// # Returns
    ///
    /// * `None`: All possible [`Branch`] are yielded.
    /// This is the case, when the iterator is called the (`2^length + 1`)-th time.
    /// * `Some(Branch)`: Otherwise.
    fn next(&mut self) -> Option<Self::Item> {
        let current_tick: u128 = self.current_tick?;

        if self.end_tick != 0 && current_tick >= self.end_tick {
            self.current_tick = None; // Stops the iterator
            None
        } else {
            self.current_tick = current_tick.checked_add(1_u128);
            Some(Branch::new_unchecked(current_tick, self.length)) // Safe
        }
    }
}

/// An enum for handling errors during the creation of [`Branch`]es.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BranchError {
    /// The length of the branch is too large.
    TooLarge { length: usize },

    /// A one is beyond the supposed length.
    BitBeyondLength { number: u128, length: usize },
}

impl BranchError {
    /// Checks if the `length` is too large.
    #[inline]
    pub(crate) fn check_length(length: usize) -> Result<(), BranchError> {
        if length <= 128_usize {
            Ok(())
        } else {
            Err(BranchError::TooLarge { length })
        }
    }

    /// Checks if there is any bit set to one beyond the `length`.
    #[inline]
    pub(crate) fn check_bits(number: u128, length: usize) -> Result<(), BranchError> {
        if 128_usize - number.leading_zeros() as usize <= length {
            Ok(())
        } else {
            Err(BranchError::BitBeyondLength { number, length })
        }
    }
}

impl fmt::Display for BranchError {
    fn fmt(&self, format: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BranchError::TooLarge { length } => write!(
                format,
                "Branch length of {} is too large. Lengths only supported up to 128.",
                length
            ),
            BranchError::BitBeyondLength { number, length } => write!(
                format,
                "The number {:b} has a 1 beyond its supposed length of {}",
                number, length
            ),
        }
    }
}

impl std::error::Error for BranchError {}
