import React from 'react';
import MenuItem from '../MenuItem';
import styles from './menu.module.css';
import { MenuItem as MenuItemContract } from '../../models';

interface MenuProps {
    itemList: MenuItemContract[];
    selectedRouteKey : string;
}


export default function Menu(props: MenuProps) {

    return (
        <div className={styles.menuContainer}>
            {props.itemList && props.itemList.map((item) => {
                return (

                    <MenuItem 
                        iconComp={item.menuIconComp}
                        label={item.label} 
                        isSelected={item.routeKey === props.selectedRouteKey}
                        onClick = {() => {
                            if(item.onClick)
                                item.onClick();
                        }}
                        />                                   
                )
            })}
        </div>
    )
}