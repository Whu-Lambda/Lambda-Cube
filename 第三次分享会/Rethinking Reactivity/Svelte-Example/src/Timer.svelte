<script lang="ts">
    import { onMount } from 'svelte';

    let date = new Date();
    $: hour = date.getHours();
    $: min = date.getMinutes();
    $: sec = date.getSeconds();

    onMount( () => {
        const interval = setInterval( 
            () => {
            date = new Date();
        }, 1000);

        return () => {
            clearInterval(interval);
        };
    });
</script>

<div>
    {hour} : {min} : {sec}
</div>
