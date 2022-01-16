<script>
    import Board from "./Board.svelte";
    const title = "Tic-Tac-Toe";
</script>

<svelte:head>
    <title>{title}</title>
</svelte:head>

<h1> {title} </h1>
<Board />