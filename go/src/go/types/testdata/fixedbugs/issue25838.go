// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package p

// gin_examples from the issue

type (
	e = f
	f = g
	g = []h
	h i
	i = j
	j = e
)

type (
	e1 = []h1
	h1 e1
)

type (
	P = *T
	T P
)
