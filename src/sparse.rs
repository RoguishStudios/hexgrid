//
// Copyright 2021 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use crate::{Coordinate, Integer};
use std::collections::HashMap;

/// Sparse Hex Grid Data Storage
#[derive(Clone, Debug, Default)]
pub struct SparseHexStorage<I: Integer, D>(HashMap<Coordinate<I>, D>);

impl<I: Integer, D> SparseHexStorage<I, D> {
    /// Set Contents of Hex.
    pub fn set(&mut self, coordinate: &Coordinate<I>, data: D) {
        self.0.insert(coordinate.clone(), data);
    }
    /// Get contents of hex.
    pub fn get(&self, coordinate: &Coordinate<I>) -> Option<&D> {
        self.0.get(&coordinate)
    }
    /// Get contents of hex mutably.
    pub fn get_mut(&mut self, coordinate: &Coordinate<I>) -> Option<&mut D> {
        self.0.get_mut(&coordinate)
    }
    /// Get contents of hex mutably, calling f if data doesn't exist.
    pub fn get_mut_or_insert(
        &mut self,
        coordinate: &Coordinate<I>,
        f: fn(&Coordinate<I>) -> D,
    ) -> Option<&mut D> {
        if !self.0.contains_key(coordinate) {
            self.0.insert(coordinate.clone(), f(coordinate));
        }
        self.0.get_mut(coordinate)
    }
    /// See if hex has data.
    pub fn contains(&self, coordinate: &Coordinate<I>) -> bool {
        self.0.contains_key(coordinate)
    }
    /// Remove contents of hex.
    pub fn remove(&mut self, coordinate: &Coordinate<I>) {
        self.0.remove(&coordinate);
    }
    /// Clear contents of all hexes.
    pub fn clear(&mut self) {
        self.0.clear()
    }
}

impl<I: Integer, D> IntoIterator for SparseHexStorage<I, D> {
    type Item = (Coordinate<I>, D);
    type IntoIter = std::collections::hash_map::IntoIter<Coordinate<I>, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
