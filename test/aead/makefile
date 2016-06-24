FSTAR_HOME = D:/FStar

BITOP_ODIR = bitop
GF128_ODIR = gf128
CRYPTUTILS_ODIR = cryptutils
GCM_ODIR = gcm

# OCaml variables
OCAML = ocamlfind ocamlopt -package batteries,cryptokit,zarith -linkpkg -g -thread
OCAML_FILE = MkPrims.ml prims.ml
BITOP = Bitop.ml
GCM = Bitop.ml GF128.ml Cryptutils.ml GCM.ml

all: gcm_test

bitop_test: 
	mkdir -p $(BITOP_ODIR)
	fstar --codegen OCaml GF128.fst --odir $(BITOP_ODIR)
	cp ./lib/*.ml $(BITOP_ODIR)
	cp ./bitop_test.ml $(BITOP_ODIR)
	cd $(BITOP_ODIR) && $(OCAML) $(OCAML_FILE) $(BITOP) bitop_test.ml
	$(BITOP_ODIR)/camlprog.exe

gf128_test:
	mkdir -p $(GF128_ODIR)
	fstar --codegen OCaml GCM.fst --odir $(GF128_ODIR)

gcm_test: 
	mkdir -p $(GCM_ODIR)
	fstar --codegen OCaml Bitop.fst GF128.fst Cryptutils.fst GCM.fst --odir $(GCM_ODIR)
	cp ./lib/*.ml $(GCM_ODIR)
	cp ./gcm_test.ml $(GCM_ODIR)
	cd $(GCM_ODIR) && $(OCAML) $(OCAML_FILE) $(GCM) gcm_test.ml
	$(GCM_ODIR)/camlprog.exe

cryptutils_test:
	mkdir -p $(CRYPTUTILS_ODIR)
	fstar --codegen OCaml GCM.fst --odir $(CRYPTUTILS_ODIR)
	cp ./lib/*.ml $(CRYPTUTILS_ODIR)
	cp ./cryptutils_test.ml $(CRYPTUTILS_ODIR)
	cd $(CRYPTUTILS_ODIR) && $(OCAML) $(OCAML_FILE) $(GCM) cryptutils_test.ml
	$(CRYPTUTILS_ODIR)/camlprog.exe
