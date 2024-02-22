// Code generated by go tool dist; DO NOT EDIT.
// This is a bootstrap copy of /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/compile/internal/ssa/id.go

//line /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/compile/internal/ssa/id.go:1
// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

type ID int32

// idAlloc provides an allocator for unique integers.
type idAlloc struct {
	last ID
}

// get allocates an ID and returns it. IDs are always > 0.
func (a *idAlloc) get() ID {
	x := a.last
	x++
	if x == 1<<31-1 {
		panic("too many ids for this function")
	}
	a.last = x
	return x
}

// num returns the maximum ID ever returned + 1.
func (a *idAlloc) num() int {
	return int(a.last + 1)
}
