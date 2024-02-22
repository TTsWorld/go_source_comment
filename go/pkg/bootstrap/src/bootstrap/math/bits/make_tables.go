// Code generated by go tool dist; DO NOT EDIT.
// This is a bootstrap copy of /Users/litiantian/code/m_code/read_go_code/go_source/go/src/math/bits/make_tables.go

//line /Users/litiantian/code/m_code/read_go_code/go_source/go/src/math/bits/make_tables.go:1
// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build ignore
// +build ignore

// This program generates bits_tables.go.

package main

import (
	"bytes"
	"fmt"
	"go/format"
	"io"
	"log"
	"os"
)

var header = []byte(`// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Code generated by go run make_tables.go. DO NOT EDIT.

package bits

`)

func main() {
	buf := bytes.NewBuffer(header)

	gen(buf, "ntz8tab", ntz8)
	gen(buf, "pop8tab", pop8)
	gen(buf, "rev8tab", rev8)
	gen(buf, "len8tab", len8)

	out, err := format.Source(buf.Bytes())
	if err != nil {
		log.Fatal(err)
	}

	err = os.WriteFile("bits_tables.go", out, 0666)
	if err != nil {
		log.Fatal(err)
	}
}

func gen(w io.Writer, name string, f func(uint8) uint8) {
	// Use a const string to allow the compiler to constant-evaluate lookups at constant index.
	fmt.Fprintf(w, "const %s = \"\"+\n\"", name)
	for i := 0; i < 256; i++ {
		fmt.Fprintf(w, "\\x%02x", f(uint8(i)))
		if i%16 == 15 && i != 255 {
			fmt.Fprint(w, "\"+\n\"")
		}
	}
	fmt.Fprint(w, "\"\n\n")
}

func ntz8(x uint8) (n uint8) {
	for x&1 == 0 && n < 8 {
		x >>= 1
		n++
	}
	return
}

func pop8(x uint8) (n uint8) {
	for x != 0 {
		x &= x - 1
		n++
	}
	return
}

func rev8(x uint8) (r uint8) {
	for i := 8; i > 0; i-- {
		r = r<<1 | x&1
		x >>= 1
	}
	return
}

func len8(x uint8) (n uint8) {
	for x != 0 {
		x >>= 1
		n++
	}
	return
}
