if &cp | set nocp | endif
let s:cpo_save=&cpo
set cpo&vim
map! <S-Insert> <MiddleMouse>
inoremap <silent> <Plug>IMAP_JumpBack =IMAP_Jumpfunc('b', 0)
inoremap <silent> <Plug>IMAP_JumpForward =IMAP_Jumpfunc('', 0)
vmap <NL> <Plug>IMAP_JumpForward
nmap <NL> <Plug>IMAP_JumpForward
map :mk :! make
vmap gx <Plug>NetrwBrowseXVis
nmap gx <Plug>NetrwBrowseX
xnoremap <silent> <Plug>OCamlPrintType :call Ocaml_print_type("visual")`<
nnoremap <silent> <Plug>OCamlPrintType :call Ocaml_print_type("normal")
nnoremap <Plug>OCamlSwitchNewWin :call OCaml_switch(1)
nnoremap <Plug>OCamlSwitchEdit :call OCaml_switch(0)
map <S-Insert> <MiddleMouse>
vnoremap <silent> <Plug>NetrwBrowseXVis :call netrw#BrowseXVis()
nnoremap <silent> <Plug>NetrwBrowseX :call netrw#BrowseX(expand((exists("g:netrw_gx")? g:netrw_gx : '<cfile>')),netrw#CheckIfRemote())
vnoremap <silent> <Plug>IMAP_JumpBack `<i=IMAP_Jumpfunc('b', 0)
vnoremap <silent> <Plug>IMAP_JumpForward i=IMAP_Jumpfunc('', 0)
vnoremap <silent> <Plug>IMAP_DeleteAndJumpBack "_<Del>i=IMAP_Jumpfunc('b', 0)
vnoremap <silent> <Plug>IMAP_DeleteAndJumpForward "_<Del>i=IMAP_Jumpfunc('', 0)
nnoremap <silent> <Plug>IMAP_JumpBack i=IMAP_Jumpfunc('b', 0)
nnoremap <silent> <Plug>IMAP_JumpForward i=IMAP_Jumpfunc('', 0)
imap <NL> <Plug>IMAP_JumpForward
let &cpo=s:cpo_save
unlet s:cpo_save
set autoindent
set backspace=indent,eol,start
set errorformat=%EFile\ \"%f\"\\,\ line\ %l\\,\ characters\ %c-%*\\d:,%EFile\ \"%f\"\\,\ line\ %l\\,\ character\ %c:%m,%+EReference\ to\ unbound\ regexp\ name\ %m,%Eocamlyacc:\ e\ -\ line\ %l\ of\ \"%f\"\\,\ %m,%Wocamlyacc:\ w\ -\ %m,%-Zmake%.%#,%C%m,%D%*\\a[%*\\d]:\ Entering\ directory\ `%f',%X%*\\a[%*\\d]:\ Leaving\ directory\ `%f',%D%*\\a:\ Entering\ directory\ `%f',%X%*\\a:\ Leaving\ directory\ `%f',%DMaking\ %*\\a\ in\ %f
set fileencodings=ucs-bom,utf-8,default,latin1
set grepprg=grep\\
set guifont=Monospace\ 14
set helplang=en
set nomodeline
set mouse=a
set pastetoggle=<F2>
set printoptions=paper:a4
set ruler
set runtimepath=~/.vim,/var/lib/vim/addons,/usr/share/vim/vimfiles,/usr/share/vim/vim74,/usr/share/vim/vimfiles/after,/var/lib/vim/addons/after,~/.vim/after,~/.opam/system/share/merlin/vim
set shiftwidth=4
set softtabstop=4
set suffixes=.bak,~,.swp,.o,.info,.aux,.log,.dvi,.bbl,.blg,.brf,.cb,.ind,.idx,.ilg,.inx,.out,.toc
set tabstop=4
set termencoding=utf-8
set window=57
" vim: set ft=vim :
