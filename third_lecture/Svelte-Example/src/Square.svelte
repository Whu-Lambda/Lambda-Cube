<!--Square Component-->
<script lang="ts">
export let value: any;
export let handleClick: svelte.JSX.MouseEventHandler<HTMLButtonElement>;
</script>

<style>
    .square {
      flex: 1 0 25%;
      width: 50px;
      height: 70px;
      background-color: whitesmoke;
      border: 2px solid black;
      margin: 5px;
      padding: 5px;
      font-size: 20px;
      text-align: center;
    }
  
    .square:hover {
      border: 2px solid red;
    }
</style>

<button class="square" on:click={handleClick}> {value || ""} </button>